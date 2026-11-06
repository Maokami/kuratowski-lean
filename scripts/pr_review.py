"""신뢰한 기본 브랜치에서 PR 자료 준비, 결과 검증, 게시를 수행한다. PR 코드는 실행하지 않는다."""

import base64
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import quote
from urllib.request import Request, urlopen


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

    def get_pr(self, number):
        return self.request(f"/repos/{self.repo}/pulls/{number}")

    def merge_when_ready(self, number, sha):
        subprocess.run(["gh", "pr", "merge", str(number), "--repo", self.repo,
                        "--auto", "--squash", "--match-head-commit", sha], check=True)


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


def prepare(api, number):
    pr = api.get_pr(number)
    if not eligible(pr, api.repo):
        raise ValueError("자동 검토 대상은 같은 저장소의 신뢰한 작성자가 연 준비된 PR입니다.")
    if not 0 < pr["changed_files"] <= 100:
        raise ValueError("자동 검토 범위는 변경 파일 1~100개입니다.")
    files = api.request(f"/repos/{api.repo}/pulls/{number}/files?per_page=100")
    if len(files) != pr["changed_files"]:
        raise ValueError("변경 파일 목록이 완전하지 않습니다.")
    root = Path(".review-input")
    (root / "files").mkdir(parents=True, exist_ok=True)
    entries = []
    total = 0
    for i, file in enumerate(files):
        entry = {"path": file["filename"], "status": file["status"]}
        for side, sha in [("before", pr["base"]["sha"]), ("after", pr["head"]["sha"])]:
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
    if current["head"]["sha"] != pr["head"]["sha"] or current["base"]["sha"] != pr["base"]["sha"]:
        raise ValueError("자료 준비 중 PR이 바뀌었습니다.")
    manifest = {"repository": api.repo, "number": number, "sha": pr["head"]["sha"],
                "base_sha": pr["base"]["sha"], "files": entries}
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


def publish(api, number, manifest, result):
    if manifest["repository"] != api.repo or manifest["number"] != number:
        raise ValueError("다른 PR의 artifact입니다.")
    validate(json.dumps(result), manifest, "success", (api.token,))
    pr = api.get_pr(number)
    if not eligible(pr, api.repo) or pr["head"]["sha"] != manifest["sha"]:
        raise ValueError("PR이 닫혔거나 검토 후 head가 바뀌었습니다.")
    owner, name = api.repo.split("/")
    protection = api.request("/graphql", {
        "query": "query($owner:String!,$name:String!){repository(owner:$owner,name:$name){branchProtectionRules(first:100){nodes{pattern requiresStatusChecks requiresStrictStatusChecks requiredStatusCheckContexts}}}}",
        "variables": {"owner": owner, "name": name}}, "POST")
    rules = protection.get("data", {}).get("repository", {}).get("branchProtectionRules", {}).get("nodes", [])
    if not any(rule["pattern"] == "main" and rule["requiresStatusChecks"]
               and rule["requiresStrictStatusChecks"]
               and {"Lean CI", "AI review"}.issubset(rule["requiredStatusCheckContexts"]) for rule in rules):
        raise ValueError("main의 필수 CI·AI 리뷰 보호 규칙이 없습니다. 자동 머지를 중단합니다.")
    marker = "<!-- kuratowski-ai-review -->"
    body = (f"{marker}\nAI 리뷰: **{result['verdict']}**\n\n"
            f"검토 SHA: `{manifest['sha']}`\n\n{result['summary']}\n\n")
    body += "\n".join(f"- `{f['path']}`: {f['reason']}" for f in result["findings"])
    body += f"\n\n[실행 근거]({os.environ['RUN_URL']}) · 파일 목록은 모델의 자기 보고입니다.\n"
    comments = api.request(f"/repos/{api.repo}/issues/{number}/comments?per_page=100")
    previous = next((c for c in comments if c["user"]["login"] == "github-actions[bot]" and c["body"].startswith(marker)), None)
    if previous:
        api.request(f"/repos/{api.repo}/issues/comments/{previous['id']}", {"body": body}, "PATCH")
    else:
        api.request(f"/repos/{api.repo}/issues/{number}/comments", {"body": body}, "POST")
    approved = result["verdict"] == "approve"
    api.request(f"/repos/{api.repo}/statuses/{manifest['sha']}", {
        "state": "success" if approved else "failure", "context": "AI review",
        "description": "모든 변경 파일 검토 완료" if approved else "AI 리뷰에서 수정 요청",
        "target_url": os.environ["RUN_URL"]}, "POST")
    # --auto는 필수 CI와 최신 브랜치 조건을 우회하지 않는다. --admin은 쓰지 않는다.
    # 새 커밋은 새 SHA의 AI review가 필요하므로 이전 승인이 재사용되지 않는다.
    if approved:
        api.merge_when_ready(number, manifest["sha"])


if __name__ == "__main__":
    phase = sys.argv[1]
    if phase == "prepare":
        prepare(GitHub(), pr_number())
    elif phase == "pending":
        api = GitHub()
        pr = api.get_pr(pr_number())
        if not eligible(pr, api.repo):
            raise ValueError("자동 검토 대상이 아닙니다.")
        api.request(f"/repos/{api.repo}/statuses/{pr['head']['sha']}", {
            "state": "pending", "context": "AI review", "description": "최신 PR 검토 진행 중",
            "target_url": os.environ["RUN_URL"]}, "POST")
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
        publish(GitHub(), pr_number(), manifest, result)
    else:
        raise ValueError("지원하지 않는 단계입니다.")
