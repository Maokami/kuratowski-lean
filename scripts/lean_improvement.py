"""읽기 전용 개선 조사의 예약·검증·게시. 상태는 봇 소유의 단일 이슈에 보관한다."""

import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import subprocess
import sys

GitHub = runpy.run_path(str(Path(__file__).with_name("pr_review.py")))["GitHub"]

TITLE = "[Continuous AI] Lean 개선 조사 상태"
MARKER = "<!-- lean-improvement-state:v1 -->"
REPORT = "<!-- lean-improvement-report:"
IDS = "<!-- lean-improvement-ids:"
OUT = Path(".improvement")
PROMPT = Path(".github/prompts/lean-improvement.md")
SCHEMA = Path(".github/prompts/lean-improvement-schema.json")
KINDS = {"duplicate", "assumptions", "dependency", "tactics", "documentation"}


def git(*args):
    return subprocess.check_output(["git", *args], text=True).strip()


def source():
    files = sorted(git("ls-files", "Kuratowski/*.lean").splitlines())
    if not files or any(not re.fullmatch(r"Kuratowski/[A-Za-z0-9_]+\.lean", p) for p in files):
        raise ValueError("Lean 파일 목록이 잘못되었습니다.")
    texts = {}
    for p in files:
        path = Path(p)
        if path.is_symlink() or not path.is_file():
            raise ValueError("일반 소스 파일만 읽습니다.")
        texts[p] = path.read_text()
    digest = hashlib.sha256()
    for p in files + [str(PROMPT), str(SCHEMA), "scripts/lean_improvement.py", "AGENTS.md",
                      "CLAUDE.md", ".github/workflows/lean-improvement.yml"]:
        digest.update(p.encode() + b"\0" + Path(p).read_bytes() + b"\0")
    batches = [files[i:i + 4] for i in range(0, len(files), 4)]
    return texts, batches, digest.hexdigest()


def all_issues(api):
    result = []
    for page in range(1, 11):
        items = api.request(f"/repos/{api.repo}/issues?state=all&per_page=100&page={page}")
        result.extend(items)
        if len(items) < 100:
            return result
    raise ValueError("이슈 이력을 끝까지 읽지 못했습니다.")


def owned(issue):
    return ("pull_request" not in issue
            and issue.get("user", {}).get("login") == "github-actions[bot]")


def load_state(issues):
    matches = [i for i in issues if owned(i) and i.get("title") == TITLE
               and (i.get("body") or "").startswith(MARKER + "\n")]
    if len(matches) > 1:
        raise ValueError("상태 이슈가 중복되었습니다.")
    if not matches:
        return None, {"version": 1, "batches": {}, "seen": []}
    issue = matches[0]
    state = json.loads(issue["body"].split("\n", 1)[1])
    if (set(state) != {"version", "batches", "seen"} or state["version"] != 1
            or not isinstance(state["batches"], dict) or not isinstance(state["seen"], list)
            or len(state["seen"]) > 300
            or any(not isinstance(k, str) or not re.fullmatch(r"[0-9a-f]{64}", k)
                   for k in state["seen"])):
        raise ValueError("상태 이슈 형식이 잘못되었습니다.")
    for key, entry in state["batches"].items():
        if (not re.fullmatch(r"[0-9]{1,3}", key) or not isinstance(entry, dict)
                or set(entry) != {"digest", "attempts", "status", "run_id"}
                or not re.fullmatch(r"[0-9a-f]{64}", entry["digest"])
                or type(entry["attempts"]) is not int or not 1 <= entry["attempts"] <= 2
                or entry["status"] not in {"pending", "success", "error"}
                or not re.fullmatch(r"[0-9]+", entry["run_id"])):
            raise ValueError("조사 이력이 잘못되었습니다.")
    return issue["number"], state


def save_state(api, number, state):
    body = MARKER + "\n" + json.dumps(state, ensure_ascii=False, indent=2)
    if len(body.encode()) > 50000:
        raise ValueError("상태가 커졌습니다. 유지관리자의 이력 정리가 필요합니다.")
    if number is None:
        return api.request(f"/repos/{api.repo}/issues", {"title": TITLE, "body": body})["number"]
    api.request(f"/repos/{api.repo}/issues/{number}", {"body": body}, "PATCH")
    return number


def select_batch(batches, state, digest, requested, retry):
    if requested == "auto":
        if retry:
            raise ValueError("재시도는 batch 번호를 지정해야 합니다.")
        options = sorted(range(len(batches)), key=lambda i: (
            int(state["batches"].get(str(i), {}).get("run_id", "0")), i))
    elif re.fullmatch(r"[0-9]{1,3}", requested) and int(requested) < len(batches):
        options = [int(requested)]
    else:
        raise ValueError("등록되지 않은 batch입니다.")
    for index in options:
        old = state["batches"].get(str(index), {})
        if old.get("digest") != digest:
            return index, 1
        if retry and old.get("status") != "success" and old["attempts"] < 2:
            return index, old["attempts"] + 1
    return None


def prepare(api):
    requested = os.environ.get("REVIEW_BATCH", "auto")
    retry = os.environ.get("RETRY_FAILED", "false")
    if retry not in {"true", "false"}:
        raise ValueError("retry 입력이 잘못되었습니다.")
    _, batches, digest = source()
    # 입력을 상태 쓰기 전에 검사한다.
    select_batch(batches, {"batches": {}}, digest, requested, retry == "true")
    if api.request(f"/repos/{api.repo}/git/ref/heads/main")["object"]["sha"] != git("rev-parse", "HEAD"):
        return {"run": "false"}
    issues = all_issues(api)
    number, state = load_state(issues)
    selected = select_batch(batches, state, digest, requested, retry == "true")
    if selected is None:
        return {"run": "false"}
    index, attempts = selected
    plan = {"sha": git("rev-parse", "HEAD"), "batch": index, "digest": digest,
            "required_files": batches[index], "run_id": os.environ["GITHUB_RUN_ID"],
            "requested_model": "sonnet", "policy": "read-only-v1"}
    state["batches"][str(index)] = {
        "digest": digest, "attempts": attempts, "status": "pending", "run_id": plan["run_id"]}
    save_state(api, number, state)  # 실패·중단도 같은 입력으로 무한 반복되지 않도록 먼저 예약한다.
    OUT.mkdir(exist_ok=True)
    (OUT / "plan.json").write_text(json.dumps(plan, ensure_ascii=False, indent=2) + "\n")
    return {"run": "true", "schema": json.dumps(json.loads(SCHEMA.read_text()), separators=(",", ":"))}


def text(value, maximum):
    if not isinstance(value, str) or not value.strip() or len(value) > maximum:
        raise ValueError("문자열 필드가 잘못되었습니다.")


def validate(raw, plan, conclusion, secrets=()):
    if conclusion != "success" or len(raw.encode()) > 40000:
        raise ValueError("조사가 실패했거나 결과가 너무 큽니다.")
    data = json.loads(raw)
    serialized = json.dumps(data, ensure_ascii=False)
    if any(s and s in serialized for s in secrets) or re.search(
            r"(?:gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|sk-ant-[A-Za-z0-9_-]{20,})", serialized):
        raise ValueError("인증 정보가 포함된 결과는 보관하지 않습니다.")
    if (not isinstance(data, dict)
            or set(data) != {"sha", "batch", "reviewed_files", "summary", "candidates"}
            or data["sha"] != plan["sha"] or type(data["batch"]) is not int
            or data["batch"] != plan["batch"]):
        raise ValueError("조사 대상과 결과가 다릅니다.")
    sources, batches, digest = source()
    if (plan["sha"] != git("rev-parse", "HEAD") or plan["digest"] != digest
            or plan["required_files"] != batches[plan["batch"]]):
        raise ValueError("입력 소스가 바뀌었습니다.")
    files = data["reviewed_files"]
    if (not isinstance(files, list) or not all(isinstance(p, str) and p in sources for p in files)
            or len(files) != len(set(files)) or not set(plan["required_files"]).issubset(files)):
        raise ValueError("검토 파일이 누락되었거나 허용되지 않았습니다.")
    text(data["summary"], 2000)
    candidates = data["candidates"]
    if not isinstance(candidates, list) or len(candidates) > 3:
        raise ValueError("후보는 최대 3개입니다.")
    ids = set()
    for c in candidates:
        if not isinstance(c, dict) or set(c) != {
                "path", "declaration", "kind", "risk", "title", "reason", "proposal", "evidence"}:
            raise ValueError("후보 형식이 잘못되었습니다.")
        if (c["path"] not in plan["required_files"] or c["kind"] not in KINDS
                or c["risk"] not in {"proof-only", "manual"}):
            raise ValueError("후보 범위가 잘못되었습니다.")
        for name, limit in (("declaration", 160), ("title", 100), ("reason", 2000), ("proposal", 2000)):
            text(c[name], limit)
        if not re.search(r"\b(?:theorem|lemma|def|abbrev|structure|inductive)\s+"
                         + re.escape(c["declaration"].split(".")[-1]) + r"(?=\s|[({:\[])", sources[c["path"]]):
            raise ValueError("후보 선언을 소스에서 찾지 못했습니다.")
        evidence = c["evidence"]
        if not isinstance(evidence, list) or not 1 <= len(evidence) <= 3:
            raise ValueError("소스 근거가 필요합니다.")
        for e in evidence:
            if (not isinstance(e, dict) or set(e) != {"path", "line", "quote"}
                    or e["path"] not in files or type(e["line"]) is not int or e["line"] < 1):
                raise ValueError("근거 위치가 잘못되었습니다.")
            text(e["quote"], 1500)
            rest = "\n".join(sources[e["path"]].splitlines()[e["line"] - 1:])
            if not rest.startswith(e["quote"]):
                raise ValueError("인용문과 실제 소스 위치가 다릅니다.")
        key = candidate_id(c)
        if key in ids:
            raise ValueError("중복 후보입니다.")
        ids.add(key)
    return data


def candidate_id(c):
    return hashlib.sha256(json.dumps([c["path"], c["declaration"], c["kind"]]).encode()).hexdigest()


def safe(value):
    return value.replace("@", "＠").replace("<", "&lt;").replace(">", "&gt;")


def posted_ids(issues):
    result = set()
    for i in issues:
        body = i.get("body") or ""
        if not owned(i) or not body.startswith(REPORT):
            continue
        lines = body.splitlines()
        if len(lines) < 2 or not lines[1].startswith(IDS) or not lines[1].endswith(" -->"):
            raise ValueError("게시 후보 ID를 복구하지 못했습니다.")
        ids = json.loads(lines[1][len(IDS):-4])
        if (not isinstance(ids, list) or not 1 <= len(ids) <= 3
                or any(not isinstance(k, str) or not re.fullmatch(r"[0-9a-f]{64}", k) for k in ids)):
            raise ValueError("게시 후보 ID 형식이 잘못되었습니다.")
        result.update(ids)
    return result


def publish(api):
    plan = json.loads((OUT / "plan.json").read_text())
    data = validate((OUT / "review.json").read_text(), plan, "success")
    issues = all_issues(api)
    number, state = load_state(issues)
    entry = state["batches"].get(str(plan["batch"]), {})
    if (number is None or plan["run_id"] != os.environ["GITHUB_RUN_ID"]
            or entry.get("run_id") != plan["run_id"] or entry.get("digest") != plan["digest"]
            or entry.get("status") != "pending"):
        raise ValueError("현재 실행이 예약한 조사가 아닙니다.")
    if api.request(f"/repos/{api.repo}/git/ref/heads/main")["object"]["sha"] != plan["sha"]:
        raise ValueError("main이 바뀌었습니다. 오래된 결과는 게시하지 않습니다.")
    # 게시 뒤 상태 저장이 실패했어도, 실제 게시한 ID를 이전 보고서에서 복구한다.
    state["seen"] = sorted(set(state["seen"]) | posted_ids(issues))
    fresh = [c for c in data["candidates"] if candidate_id(c) not in state["seen"]]
    if len(state["seen"]) + len(fresh) > 300:
        raise ValueError("후보 이력을 유지관리자가 정리해야 합니다.")
    marker = REPORT + str(plan["batch"]) + ":" + plan["digest"] + ":" + plan["run_id"] + " -->"
    if fresh:
        body = marker + "\n" + IDS + json.dumps([candidate_id(c) for c in fresh]) + " -->\n"
        body += "AI가 제안한 미검증 후보입니다. 코드 수정·PR 생성은 수행하지 않았습니다.\n\n"
        body += f"소스: `{plan['sha']}` · batch {plan['batch']} · run {plan['run_id']}\n\n"
        body += safe(data["summary"]) + "\n"
        for c in fresh:
            body += "\n### " + safe(c["title"]) + "\n\n"
            body += safe(f"{c['path']} · {c['declaration']} · {c['kind']} · {c['risk']}") + "\n\n"
            body += safe(c["reason"]) + "\n\n" + safe(c["proposal"]) + "\n\n"
            for e in c["evidence"]:
                body += f"- [{safe(e['path'])}:{e['line']}](https://github.com/{api.repo}/blob/{plan['sha']}/{e['path']}#L{e['line']})\n"
        api.request(f"/repos/{api.repo}/issues", {
            "title": f"[Lean 개선 후보] batch {plan['batch']} ({len(fresh)}건)", "body": body})
    state["seen"] += [candidate_id(c) for c in fresh if candidate_id(c) not in state["seen"]]
    entry["status"] = "success"
    save_state(api, number, state)
    print(f"candidates={len(data['candidates'])} new={len(fresh)}")


def error(api):
    number, state = load_state(all_issues(api))
    if number is not None:
        for entry in state["batches"].values():
            if entry["run_id"] == os.environ["GITHUB_RUN_ID"] and entry["status"] == "pending":
                entry["status"] = "error"
        save_state(api, number, state)


def main():
    if sys.argv[1:] == ["validate"]:
        plan = json.loads((OUT / "plan.json").read_text())
        data = validate(os.environ["REVIEW_JSON"], plan, os.environ["REVIEW_CONCLUSION"],
                        (os.environ.get("GITHUB_TOKEN"), os.environ.get("REVIEW_OAUTH_TOKEN")))
        (OUT / "review.json").write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    elif sys.argv[1:] == ["prepare"]:
        outputs = prepare(GitHub())
        with open(os.environ["GITHUB_OUTPUT"], "a") as f:
            for key, value in outputs.items():
                f.write(f"{key}={value}\n")
    elif sys.argv[1:] == ["publish"]:
        publish(GitHub())
    elif sys.argv[1:] == ["error"]:
        error(GitHub())
    else:
        raise ValueError("사용법: lean_improvement.py prepare|validate|publish|error")


if __name__ == "__main__":
    main()
