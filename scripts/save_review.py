"""빈 결과나 다른 커밋의 결과를 성공으로 처리하지 않고 검토 보고서를 보관한다."""

import json
import os
from pathlib import Path


def validate_review(raw, expected_sha, conclusion, secrets=()):
    if conclusion != "success":
        raise ValueError("Claude 검토가 성공하지 않았습니다.")
    data = json.loads(raw)
    if not isinstance(data, dict) or data.get("sha") != expected_sha:
        raise ValueError("검토 SHA가 실행 대상과 다릅니다.")
    files = data.get("reviewed_files")
    if not isinstance(files, list) or not files:
        raise ValueError("실제로 읽은 파일 목록이 필요합니다.")
    root = Path.cwd().resolve()
    for file in files:
        if not isinstance(file, str) or Path(file).is_absolute():
            raise ValueError("검토 파일은 저장소 상대 경로여야 합니다.")
        resolved = (root / file).resolve()
        if root not in resolved.parents or not resolved.is_file():
            raise ValueError("검토 파일이 저장소 안에 없습니다.")
        if any(part == ".git" or part.startswith(".env")
               for part in resolved.relative_to(root).parts):
            raise ValueError("인증 설정 파일은 검토 대상이 아닙니다.")
    if not isinstance(data.get("report"), str) or not data["report"].strip():
        raise ValueError("검토 보고서가 비어 있습니다.")
    serialized = json.dumps(data, ensure_ascii=False)
    if any(secret and secret in serialized for secret in secrets):
        raise ValueError("인증 정보가 포함된 결과는 보관하지 않습니다.")
    return data


if __name__ == "__main__":
    data = validate_review(
        os.environ["REVIEW_JSON"], os.environ["EXPECTED_SHA"],
        os.environ["REVIEW_CONCLUSION"],
        (os.environ["REVIEW_GITHUB_TOKEN"], os.environ["REVIEW_OAUTH_TOKEN"]),
    )
    out = Path("review-output")
    out.mkdir(exist_ok=True)
    (out / "review.json").write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    (out / "review.md").write_text(data["report"] + "\n")
    # 모델이 쓴 Markdown을 실행 요약에 직접 삽입하지 않는다.
    with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as summary:
        summary.write("검토 결과를 검증했습니다. lean-blueprint-review artifact를 확인하세요.\n")
