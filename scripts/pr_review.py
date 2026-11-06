"""신뢰한 기본 브랜치에서 PR 자료 준비, 결과 검증, 게시, 머지를 수행한다. PR 코드는 실행하지 않는다.

단계 (`python3 -I scripts/pr_review.py <단계>`):
* pending  : 현재 head에 "AI review" pending 상태를 쓰고, 남아 있는 auto-merge를 끈다.
             확인한 head SHA를 GITHUB_OUTPUT의 sha로 내보낸다.
* prepare  : PR의 변경 파일 before(merge base)/after(head)를 번호 붙인 .txt 자료로 받는다.
* validate : 모델 결과를 manifest와 대조해 검증한다.
* publish  : 리뷰 댓글과 "AI review" 상태를 쓰고, 승인이며 보호 경로를 건드리지 않았으면
             정확한 head의 신뢰한 CI 성공을 정해진 시간 안에서 기다린 뒤 그 SHA로 squash 머지한다.

* error    : 실행이 실패했을 때 PR_SHA의 "AI review"가 아직 이 워크플로가 쓴 pending이면 error로 바꾼다.
             이미 최종 판정(success/failure)이 있으면 덮어쓰지 않는다. 모델 자료나 secret을 쓰지 않는다.

publish는 GITHUB_OUTPUT에 merge_state를 쓴다. ci_failed와 timeout이면 0이 아닌 값으로 끝난다.
"""

import base64
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from urllib.error import HTTPError
from urllib.parse import quote
from urllib.request import Request, urlopen

REQUIRED_CONTEXTS = {"Lean CI", "AI review"}
GITHUB_ACTIONS_APP_ID = 15368  # 필수 검사는 GitHub Actions가 만든 것만 인정한다 (ruleset의 integration_id)
CI_WORKFLOW_PATH = ".github/workflows/ci.yml"
CI_JOB_NAME = "Lean CI"
# 이 경로를 바꾸는 PR은 AI 승인과 CI가 통과해도 자동으로 머지하지 않는다 (사람이 머지한다).
PROTECTED_PREFIXES = (".github/", "scripts/")
PROTECTED_FILES = {"lakefile.toml", "lake-manifest.json", "lean-toolchain", "KuratowskiAudit.lean"}
WAIT_SECONDS = 40 * 60
POLL_SECONDS = 30
FAILING_STATES = {"ci_failed", "timeout"}
MARKER = "<!-- kuratowski-ai-review -->"


class GitHub:
    def __init__(self):
        self.repo = os.environ["GITHUB_REPOSITORY"]
        self.token = os.environ["GITHUB_TOKEN"]

    def request(self, path, data=None, method=None):
        url = "https://api.github.com" + path
        request = Request(url, data=None if data is None else json.dumps(data).encode(),
                          method=method, headers={"Authorization": "Bearer " + self.token,
                          "Accept": "application/vnd.github+json", "X-GitHub-Api-Version": "2022-11-28"})
        with urlopen(request, timeout=60) as response:
            raw = response.read()
        return json.loads(raw) if raw else None

    def graphql(self, query, variables):
        result = self.request("/graphql", {"query": query, "variables": variables}, "POST")
        if not isinstance(result, dict) or result.get("errors"):
            raise ValueError(f"GraphQL 요청이 실패했습니다: {result and result.get('errors')}")
        return result["data"]

    def get_pr(self, number):
        pr = self.request(f"/repos/{self.repo}/pulls/{number}")
        if not isinstance(pr, dict):
            raise ValueError("PR 정보를 읽지 못했습니다.")
        return pr

    def merge(self, number, sha):
        """정확한 head SHA로 squash 머지한다. 200(머지), 405(아직 머지 불가), 409(head 변경)를 돌려준다.

        HTTP 200이어도 응답의 merged가 true가 아니면 머지된 것으로 보지 않는다.
        """
        try:
            response = self.request(f"/repos/{self.repo}/pulls/{number}/merge",
                                    {"sha": sha, "merge_method": "squash"}, "PUT")
        except HTTPError as error:
            if error.code in (405, 409):
                return error.code
            raise
        if not isinstance(response, dict) or response.get("merged") is not True:
            raise ValueError("머지 응답에서 merged=true를 확인하지 못했습니다.")
        return 200

    def cleanup_branch(self, number, sha):
        """머지한 PR의 head만 삭제한다. lease로 새 push와 삭제 사이의 경쟁을 막는다."""
        pr = self.get_pr(number)
        if (pr.get("merged") is not True or pr["head"]["sha"] != sha
                or (pr["head"].get("repo") or {}).get("full_name") != self.repo
                or pr["base"]["ref"] != "main" or pr["head"]["ref"] == "main"):
            raise ValueError("머지된 작업 브랜치임을 확인하지 못했습니다.")
        ref = "refs/heads/" + pr["head"]["ref"]
        # 토큰 값은 argv/URL/파일에 넣지 않는다. credential helper만 환경에서 읽는다.
        result = subprocess.run([
            "git", "-c", "credential.helper=", "-c",
            'credential.helper=!f() { echo username=x-access-token; echo "password=$GITHUB_TOKEN"; }; f',
            "push", "--force-with-lease=" + ref + ":" + sha,
            "https://github.com/" + self.repo + ".git", ":" + ref], check=False)
        if result.returncode:
            print("branch_cleanup=retained (새 커밋 또는 삭제 권한 확인 필요)")
        else:
            print("branch_cleanup=deleted")
        return result.returncode == 0


def pr_number():
    value = os.environ["PR_NUMBER"]
    if not re.fullmatch(r"[1-9][0-9]{0,8}", value):
        raise ValueError("잘못된 PR 번호입니다.")
    return int(value)


def eligible(pr, repo):
    return (pr["state"] == "open" and not pr["draft"]
            and pr["head"]["repo"] is not None and pr["head"]["repo"]["full_name"] == repo
            and pr["base"]["ref"] == "main"
            and pr["author_association"] in {"OWNER", "MEMBER", "COLLABORATOR"})


def is_protected(path):
    return isinstance(path, str) and (path.startswith(PROTECTED_PREFIXES) or path in PROTECTED_FILES)


def protected_changes(manifest):
    """보호 경로를 바꾼 파일 (이름을 바꾼 경우 옛 경로도 본다)."""
    hits = []
    for entry in manifest["files"]:
        for path in (entry.get("path"), entry.get("previous_path")):
            if is_protected(path) and path not in hits:
                hits.append(path)
    return hits


def neutralize(text):
    """모델이 쓴 글을 댓글에 넣기 전에 @멘션과 HTML 주석을 무력화한다."""
    return text.replace("@", "@​").replace("<!--", "&lt;!--")


def disable_auto_merge(api, pr):
    """이전에 켜진 auto-merge가 있으면 끈다. 머지는 publish가 정확한 SHA로만 한다."""
    if pr.get("auto_merge"):
        api.graphql("mutation($id:ID!){disablePullRequestAutoMerge(input:{pullRequestId:$id}){clientMutationId}}",
                    {"id": pr["node_id"]})


def require_protection(api):
    """main에 strict 필수 검사 "Lean CI"와 "AI review"가 있는 ruleset 규칙이 걸려 있는지 확인한다.
    두 검사 모두 GitHub Actions(integration_id 15368)가 만든 것만 인정하도록 묶여 있어야 한다.

    브랜치 보호 API는 Administration 권한이 필요해 GITHUB_TOKEN으로 읽을 수 없으므로,
    Metadata 읽기로 되는 `rules/branches/main`을 쓴다.
    """
    rules = api.request(f"/repos/{api.repo}/rules/branches/main?per_page=100")
    checks = [r for r in rules or [] if isinstance(r, dict) and r.get("type") == "required_status_checks"]
    strict = any(r.get("parameters", {}).get("strict_required_status_checks_policy") is True for r in checks)
    contexts = {c.get("context") for r in checks
                for c in r.get("parameters", {}).get("required_status_checks", [])
                if c.get("integration_id") == GITHUB_ACTIONS_APP_ID}
    if not strict or not REQUIRED_CONTEXTS.issubset(contexts):
        raise ValueError("main의 strict 필수 검사(Lean CI, AI review, GitHub Actions 출처) ruleset이 없습니다. "
                         "자동 머지를 중단합니다.")


def pending(api, number):
    """현재 head에 pending을 쓰고 남은 auto-merge를 끈다. 확인한 head SHA를 돌려준다."""
    pr = api.get_pr(number)
    if not eligible(pr, api.repo):
        raise ValueError("자동 검토 대상이 아닙니다.")
    sha = pr["head"]["sha"]
    disable_auto_merge(api, pr)
    api.request(f"/repos/{api.repo}/statuses/{sha}", {
        "state": "pending", "context": "AI review", "description": "최신 PR 검토 진행 중",
        "target_url": os.environ["RUN_URL"]}, "POST")
    return sha


def prepare(api, number):
    pr = api.get_pr(number)
    if not eligible(pr, api.repo):
        raise ValueError("자동 검토 대상은 같은 저장소의 신뢰한 작성자가 연 준비된 PR입니다.")
    if not 0 < pr["changed_files"] <= 100:
        raise ValueError("자동 검토 범위는 변경 파일 1~100개입니다.")
    head, base = pr["head"]["sha"], pr["base"]["sha"]
    # before는 PR 변경 목록과 같은 기준인 merge base에서 읽는다 (base 끝이 아니다).
    compare = api.request(f"/repos/{api.repo}/compare/{base}...{head}")
    merge_base = compare["merge_base_commit"]["sha"]
    if not re.fullmatch(r"[0-9a-f]{40}", merge_base):
        raise ValueError("merge base를 확인하지 못했습니다.")
    files = api.request(f"/repos/{api.repo}/pulls/{number}/files?per_page=100")
    if len(files) != pr["changed_files"]:
        raise ValueError("변경 파일 목록이 완전하지 않습니다.")
    root = Path(".review-input")
    (root / "files").mkdir(parents=True, exist_ok=True)
    entries = []
    total = 0
    for i, file in enumerate(files):
        entry = {"path": file["filename"], "status": file["status"]}
        if file.get("previous_filename"):
            entry["previous_path"] = file["previous_filename"]
        for side, sha in [("before", merge_base), ("after", head)]:
            if (side == "before" and file["status"] == "added") or (side == "after" and file["status"] == "removed"):
                entry[side] = None
                continue
            name = file.get("previous_filename", file["filename"]) if side == "before" else file["filename"]
            data = api.request(f"/repos/{api.repo}/contents/{quote(name, safe='/')}?ref={sha}")
            if data.get("type") != "file" or data.get("encoding") != "base64" or data["size"] > 100_000:
                raise ValueError("지원하지 않거나 너무 큰 변경 파일입니다.")
            content = base64.b64decode(data["content"]).decode("utf-8")
            total += len(content.encode())
            if total > 2_000_000:
                raise ValueError("검토 자료가 2MB를 초과합니다.")
            path = root / "files" / f"{i}-{side}.txt"
            path.write_text(content)
            entry[side] = str(path)
        entries.append(entry)
    # 목록을 읽는 동안 새 커밋이 들어왔으면 이전 결과로 진행하지 않는다.
    current = api.get_pr(number)
    if current["head"]["sha"] != head or current["base"]["sha"] != base:
        raise ValueError("자료 준비 중 PR이 바뀌었습니다.")
    manifest = {"repository": api.repo, "number": number, "sha": head, "base_sha": base,
                "merge_base_sha": merge_base, "files": entries}
    (root / "manifest.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2))


def validate(raw, manifest, conclusion, secrets=()):
    if conclusion != "success":
        raise ValueError("모델 실행이 성공하지 않았습니다.")
    result = json.loads(raw)
    if not isinstance(result, dict) or result.get("sha") != manifest["sha"]:
        raise ValueError("검토 SHA가 다릅니다.")
    if result.get("verdict") not in {"approve", "request_changes"}:
        raise ValueError("유효한 판정이 없습니다.")
    paths = {file["path"] for file in manifest["files"]}
    reviewed = result.get("reviewed_files")
    if not isinstance(reviewed, list) or not all(isinstance(p, str) for p in reviewed) or not paths.issubset(reviewed):
        raise ValueError("변경 파일 검토가 누락되었습니다.")
    if not isinstance(result.get("summary"), str) or not result["summary"].strip():
        raise ValueError("검토 요약이 없습니다.")
    findings = result.get("findings")
    if not isinstance(findings, list) or len(findings) > 10:
        raise ValueError("발견 사항 형식이 잘못되었습니다.")
    for finding in findings:
        if not isinstance(finding, dict) or finding.get("path") not in paths or not isinstance(finding.get("reason"), str) or not finding["reason"].strip():
            raise ValueError("발견 사항의 경로나 근거가 잘못되었습니다.")
    if result["verdict"] == "approve" and findings:
        raise ValueError("차단 사항이 있는 보고서를 승인할 수 없습니다.")
    text = json.dumps(result, ensure_ascii=False)
    if len(text) > 40_000 or any(secret and secret in text for secret in secrets):
        raise ValueError("너무 크거나 인증 정보가 들어 있는 보고서입니다.")
    return result


def ci_state(api, sha):
    """정확한 head의 신뢰한 CI 상태: "success", "pending", "failure".

    신뢰 조건: 이 저장소의 `.github/workflows/ci.yml`이 `pull_request` 이벤트로 `sha`에서 돈 실행이고,
    그 실행의 "Lean CI" job이 성공했다. 같은 SHA의 실행이 여럿이면 가장 최근 것을 본다.
    보호 경로 가드 때문에 자동 머지 대상 PR의 ci.yml은 기본 브랜치의 것과 같다.
    """
    data = api.request(f"/repos/{api.repo}/actions/runs?head_sha={sha}&event=pull_request&per_page=100")
    runs = [run for run in (data or {}).get("workflow_runs", [])
            if run.get("path", "").split("@")[0] == CI_WORKFLOW_PATH
            and run.get("event") == "pull_request" and run.get("head_sha") == sha
            and (run.get("head_repository") or {}).get("full_name") == api.repo]
    if not runs:
        return "pending"
    run = max(runs, key=lambda r: (r.get("created_at", ""), r.get("id", 0)))
    if run.get("status") != "completed":
        return "pending"
    if run.get("conclusion") != "success":
        return "failure"
    jobs = api.request(f"/repos/{api.repo}/actions/runs/{run['id']}/jobs?per_page=100")
    named = [job for job in (jobs or {}).get("jobs", []) if job.get("name") == CI_JOB_NAME]
    if len(named) == 1 and named[0].get("status") == "completed" and named[0].get("conclusion") == "success":
        return "success"
    return "failure"


def wait_and_merge(api, number, sha, clock=time.monotonic, sleep=time.sleep,
                   timeout=WAIT_SECONDS, interval=POLL_SECONDS):
    """정확한 head의 신뢰한 CI 성공을 기다린 뒤 그 SHA로 머지한다. 기다리는 시간은 timeout 이하다.

    돌려주는 상태: merged, stale(head 변경), closed, behind(최신 main 아님·충돌), ci_failed, timeout.
    """
    deadline = clock() + timeout
    while True:
        pr = api.get_pr(number)
        if pr["head"]["sha"] != sha:
            return "stale"
        if not eligible(pr, api.repo):
            return "closed"
        state = ci_state(api, sha)
        if state == "failure":
            return "ci_failed"
        if state == "success":
            code = api.merge(number, sha)
            if code == 200:
                api.cleanup_branch(number, sha)
                return "merged"
            if code == 409:
                return "stale"
            # 405: 필수 검사가 아직 반영되지 않았거나 최신 main이 아니다.
            if api.get_pr(number).get("mergeable_state") in {"behind", "dirty"}:
                return "behind"
        if clock() + interval > deadline:
            return "timeout"
        sleep(interval)


def publish(api, number, manifest, result, clock=time.monotonic, sleep=time.sleep):
    if manifest["repository"] != api.repo or manifest["number"] != number:
        raise ValueError("다른 PR의 artifact입니다.")
    validate(json.dumps(result), manifest, "success", (api.token,))
    pr = api.get_pr(number)
    if not eligible(pr, api.repo) or pr["head"]["sha"] != manifest["sha"]:
        raise ValueError("PR이 닫혔거나 검토 후 head가 바뀌었습니다.")
    require_protection(api)
    approved = result["verdict"] == "approve"
    guarded = protected_changes(manifest)
    disable_auto_merge(api, pr)
    body = (f"{MARKER}\nAI 리뷰: **{result['verdict']}**\n\n"
            f"검토 SHA: `{manifest['sha']}`\n\n{neutralize(result['summary'])}\n\n")
    body += "\n".join(f"- `{f['path']}`: {neutralize(f['reason'])}" for f in result["findings"])
    if approved and guarded:
        body += ("\n\n보호 경로를 바꿔 자동으로 머지하지 않습니다 (사람이 머지): "
                 + ", ".join(f"`{p}`" for p in guarded))
    body += f"\n\n[실행 근거]({os.environ['RUN_URL']}) · 파일 목록은 모델의 자기 보고입니다.\n"
    comments = api.request(f"/repos/{api.repo}/issues/{number}/comments?per_page=100")
    previous = next((c for c in comments if c["user"]["login"] == "github-actions[bot]" and c["body"].startswith(MARKER)), None)
    if previous:
        api.request(f"/repos/{api.repo}/issues/comments/{previous['id']}", {"body": body}, "PATCH")
    else:
        api.request(f"/repos/{api.repo}/issues/{number}/comments", {"body": body}, "POST")
    api.request(f"/repos/{api.repo}/statuses/{manifest['sha']}", {
        "state": "success" if approved else "failure", "context": "AI review",
        "description": "모든 변경 파일 검토 완료" if approved else "AI 리뷰에서 수정 요청",
        "target_url": os.environ["RUN_URL"]}, "POST")
    if not approved:
        return "rejected"
    if guarded:
        return "guarded"
    # auto-merge를 예약하지 않는다. 정확한 head의 신뢰한 CI가 성공한 뒤에만 그 SHA로 머지한다.
    return wait_and_merge(api, number, manifest["sha"], clock, sleep)


def mark_error(api, sha):
    """이 워크플로가 남긴 pending만 error로 바꾼다. 최종 판정이 이미 있으면 그대로 둔다."""
    if not re.fullmatch(r"[0-9a-f]{40}", sha or ""):
        raise ValueError("잘못된 SHA입니다.")
    statuses = api.request(f"/repos/{api.repo}/commits/{sha}/statuses?per_page=100") or []
    latest = next((s for s in statuses if s.get("context") == "AI review"), None)
    if (latest is None or latest.get("state") != "pending"
            or (latest.get("creator") or {}).get("login") != "github-actions[bot]"):
        return False
    api.request(f"/repos/{api.repo}/statuses/{sha}", {
        "state": "error", "context": "AI review", "description": "AI 리뷰 실행 실패 (다시 실행 필요)",
        "target_url": os.environ["RUN_URL"]}, "POST")
    return True


def write_output(name, value):
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a") as output:
            output.write(f"{name}={value}\n")


if __name__ == "__main__":
    phase = sys.argv[1]
    if phase == "prepare":
        prepare(GitHub(), pr_number())
    elif phase == "pending":
        write_output("sha", pending(GitHub(), pr_number()))
    elif phase == "validate":
        manifest = json.loads(Path(".review-input/manifest.json").read_text())
        result = validate(os.environ["REVIEW_JSON"], manifest, os.environ["REVIEW_CONCLUSION"],
                          (os.environ["REVIEW_GITHUB_TOKEN"], os.environ["REVIEW_OAUTH_TOKEN"]))
        out = Path(".review-result")
        out.mkdir(exist_ok=True)
        (out / "manifest.json").write_text(json.dumps(manifest, ensure_ascii=False))
        (out / "review.json").write_text(json.dumps(result, ensure_ascii=False, indent=2))
    elif phase == "publish":
        manifest = json.loads(Path(".review-result/manifest.json").read_text())
        result = json.loads(Path(".review-result/review.json").read_text())
        state = publish(GitHub(), pr_number(), manifest, result)
        write_output("merge_state", state)
        print(f"merge_state={state}")
        sys.exit(1 if state in FAILING_STATES else 0)
    elif phase == "error":
        changed = mark_error(GitHub(), os.environ.get("PR_SHA", ""))
        print("AI review pending을 error로 바꿨습니다." if changed else "바꿀 pending 상태가 없습니다.")
    else:
        raise ValueError("지원하지 않는 단계입니다.")
