# Claude Action 검토 실험

기존 Claude 구독으로 작은 자동화의 효용부터 확인한다. gh-aw 초안은 제거했다.
여러 엔진의 비교나 공통 safe-output 정책이 필요해질 때 gh-aw를 다시 검토한다.

## 실행 범위

- `.github/workflows/lean-blueprint-review.yml`: 기본 브랜치에서 수동 실행만 허용한다.
- `.github/prompts/lean-blueprint-review.md`: Lean 진술과 블루프린트의 불일치를 최대 3개 보고한다.
- 실행할 때 `focus`를 `easy`, `tools`, `reduce`, `faces`, `main` 중 고른다.
  필수 파일의 단일 기준은 `.github/prompts/review-focus.json`이다. 선택 장을 먼저 읽고,
  관련 정의·선행 장·검사 코드를 확인한 뒤 필요한 의존 선언만 따라간다.
- GitHub 권한은 `contents: read`뿐이며 checkout은 `persist-credentials: false`로 설정한다.
  Claude Action 자체는 실행 준비 중 Git 인증을 설정하므로 인증 정보가 전혀 기록되지 않는다는 뜻은 아니다.
- Claude 도구는 Read/Glob/Grep만 제공하고 MCP와 slash command를 끈다. 셸·편집·하위 에이전트는 제공하지 않는다.
- `.git/`과 `.env*` 읽기를 거부하고, 보고서에 알려진 GitHub·OAuth 토큰이 그대로 포함되면 보관을 거부한다.
  도구 권한 규칙과 문자열 검사는 변형·인코딩된 비밀의 유출까지 보장하는 격리 장치가 아니다.
- 보고서는 별도 Python 스텝에서 검증하고 14일간 artifact로 보관한다. 이슈·댓글·PR은 만들지 않는다.
- 검토 단계 10분, 전체 job 15분, 최대 20턴, 동시 실행 하나로 제한한다.
- 등록되지 않은 focus는 모델 실행 전에 거부한다. 결과 누락, 실행 실패, SHA·focus 불일치,
  비어 있는 보고서·파일 목록, 필수 파일 누락도 실패로 처리한다.

이것은 소스 검토이며 Lean 커널 검증이 아니다. 읽었다고 보고한 파일 목록과 내용의 정확성은
사람이 확인한다. 도구 제한은 gh-aw의 네트워크 격리나 safe-outputs 전체를 재현하지 않는다.
`reviewed_files`는 모델의 자기 보고다. 필수 파일 포함 검사는 실제로 읽거나 이해했다는 증명이 아니다.
누락 시 실패하지만 읽었다고 허위 기재하는 것까지 검출하지는 못한다.
보고서는 AI가 생성한 미검증 자료다. 지시나 링크를 그대로 신뢰하지 않는다.

## 최초 GitHub 실행

첫 실행 [42191852063](https://github.com/Maokami/kuratowski-lean/actions/runs/42191852063)은
`1fda832`에서 인증·모델 응답·artifact 저장까지 성공했다. 보고서는 쉬운 방향 중심으로 파일 6개만
다뤘고, 어려운 방향은 읽지 않았다고 명시했다. 이 관찰을 바탕으로 장 선택과 필수 파일 검사를 추가했다.
새 focus 방식의 실제 실행은 별도 확인이 필요하다.

1. 주인이 게시할 GitHub 저장소를 정하고 검토한 커밋을 기본 브랜치에 올린다.
2. 로컬에서 `claude setup-token`으로 구독 토큰을 만들고 저장소 Actions secret
   `CLAUDE_CODE_OAUTH_TOKEN`에 직접 등록한다. 토큰은 파일·커밋·대화에 넣지 않는다.
3. Actions의 `Lean 블루프린트 검토`를 기본 브랜치에서 focus를 선택하여 수동 실행한다.
   읽기 전용 `github.token`을 명시하므로 이 구성에는 별도 Claude GitHub App 토큰이 필요하지 않다.
4. `lean-blueprint-review-<focus>-<SHA>` artifact의 SHA·focus, 검토 파일, 근거와 한계를 확인한다.

구독 인증은 API 청구 대신 개인 구독 한도를 사용한다. 개인 코딩과 한도를 공유하며,
추가 사용 과금 설정과 GitHub Actions 비용은 별도로 확인한다. 턴 수와 시간은 금액 상한이 아니다.
처음 5–10회는 수동으로 실행하여 맞는 발견, 오탐, 검토 시간 절감과 구독 소모를 기록한다.

## 로컬 검사

```sh
actionlint .github/workflows/lean-blueprint-review.yml
python3 -I scripts/test_save_review.py
lake build
scripts/blueprint.sh --quick
```

Action 참조는 commit SHA로 고정했다. 갱신 시 inputs/outputs와 권한을 다시 확인한다.
Conventional Commit은 `type(scope): 한국어 설명` 형식을 사용한다. 예: `ci(review): 수동 검토 추가`.

2026-11-06 로컬 검증: actionlint 통과, 보고서 검증기 정상 결과 수용 및 오류 사례 11개 거부,
임시 디렉터리에서 JSON·Markdown 보고서 저장과 빈 출력·토큰 포함 출력 실패 확인.
`scripts/blueprint.sh --quick`도 통과했다(공리 감사 11개 모듈·320개 선언, checkdecls 43개 이름).
증분 빌드 결과이며 GitHub의 실제 Action 실행 결과는 아니다.

장 선택 추가 후에는 actionlint, 다섯 장의 prepare, `test_save_review.py`를 실행했다.
다섯 장의 정상 보고서와 각 필수 파일을 하나씩 누락한 결과, focus·SHA 불일치,
잘못된 입력, 인증 경로·토큰 포함 결과를 검사했다. Lean 소스는 변경하지 않았다.

- [Claude Code GitHub Actions](https://code.claude.com/docs/en/github-actions)
- [CLI 옵션](https://code.claude.com/docs/en/cli-reference)
- [Continuous AI 개념](https://githubnext.com/projects/continuous-ai/)
