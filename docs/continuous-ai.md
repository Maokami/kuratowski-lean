# Claude Action 검토 실험

기존 Claude 구독으로 작은 자동화의 효용부터 확인한다. gh-aw 초안은 제거했다.
여러 엔진의 비교나 공통 safe-output 정책이 필요해질 때 gh-aw를 다시 검토한다.

정기적인 Lean 개선 후보 탐색과 gh-aw 신규 레인의 검토는
[지속 개선 설계안](continuous-improvement.md)에 정리했다. 현재 운영 설정과 구분되는 도입 제안이다.

## PR 자동 리뷰와 머지

완료한 작업은 기능 브랜치에서 PR로 올린다. **CI 통과 + AI 승인**이 머지 기준이다.

```text
PR 생성·새 커밋
  ├─ Lean CI: 빌드·공리 감사·import·블루프린트 선언·Python 검사
  └─ PR review: 최신 SHA에 AI review=pending
       → 신뢰한 기본 브랜치의 코드로 변경 전후를 텍스트 자료로 수집
       → 쓰기 권한 없는 Claude가 모든 변경 파일 검토
       → 별도 job이 SHA·판정·파일 목록을 검증하고 댓글·commit status 게시
       → approve이면 최신 SHA의 CI 성공을 기다린 뒤 SHA를 지정해 squash merge
main 보호: Lean CI + AI review 필수, 최신 base 필요
머지 완료 → 머지된 SHA를 확인하고 lease로 원격 작업 브랜치 삭제
```

- PR 코드는 OAuth 토큰을 가진 job에서 checkout하거나 실행하지 않는다. `pull_request_target`에서는
  신뢰한 기본 브랜치만 checkout하며, PR 파일은 숫자로 이름 붙인 `.txt` 자료로 저장한다.
- 같은 저장소의 OWNER/MEMBER/COLLABORATOR가 연, draft가 아닌 PR만 자동 리뷰·머지 대상이다.
  fork PR은 비밀 없는 CI만 실행하며 별도 유지관리자 검토가 필요하다.
- 변경 파일 100개, 파일당 100KB, 전체 자료 2MB를 넘거나 텍스트로 읽을 수 없으면 자동 검토를 중단한다.
- 모델 실패·보고서 누락·파일 누락 시 승인하지 않는다. `request_changes`이면 AI review를 실패로 기록한다.
  기존 댓글을 갱신하여 같은 PR에 보고서가 계속 쌓이지 않게 한다.
- PR 모델 검토는 최대 32턴·10분, review job은 15분으로 제한한다. 독립적인 파일 읽기는 묶어 수행한다.
  성공 결과가 있더라도 보고된 턴 수가 상한을 넘으면 Action이 실패하며 `AI review`는 error로 남는다.
  실제 PR #6의 첫 검토는 23턴으로 기존 20턴 상한을 초과해 차단됐다. 이 실패 결과는 승인으로 재사용하지 않는다.
- 게시 직전 PR 번호·최신 head SHA를 다시 확인한다. 머지도 REST API의 `sha`로 제한한다.
  지속되는 auto-merge 예약을 사용하지 않는다. main ruleset의 필수 검사가 없으면 게시/머지를 중단한다.
- 게시 job은 최신 head의 CI를 최대 40분 기다린다. base가 앞서거나 충돌이 있으면 머지하지 않는다.
  작성자가 기본 브랜치를 반영한 새 커밋을 올리면
  CI와 AI 리뷰가 다시 수행된다. 충돌을 자동으로 추측해 해결하거나 실패한 검사를 무시하지 않는다.
- `.github/**`, `scripts/**`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`,
  `KuratowskiAudit.lean` 변경은 자동 머지 대상에서 제외한다. 검사·권한을 바꾸는 PR은 독립 AI 검토와
  CI를 확인한 유지관리자가 머지한다. 새 push와 수정 요청 시 기존 auto-merge 예약도 해제한다.
- 봇 토큰으로 머지한 main push는 새 workflow를 트리거하지 않을 수 있다. PR의 CI와 리뷰 실행을
  머지 근거로 남긴다.
- 저장소의 브랜치 자동 삭제 설정만으로 봇 머지의 브랜치가 삭제되지 않는 경우가 있어 publish도
  삭제를 수행한다. 같은 저장소의 머지된 PR만 대상으로 하며 main은 제외한다. `--force-with-lease`로
  머지 뒤 새 커밋이 올라온 브랜치는 보존한다. 삭제 실패는 이미 성공한 머지를 취소하지 않으며 로그에 남긴다.
- AI의 `reviewed_files`와 승인은 자기 보고·추론이다. Lean 커널 검증과 다른 증거이며 진술의 정확성을
  보장하지 않는다. 사용자가 선택한 운영 정책에 따라 사람 승인 없이 머지가 진행된다.

`pr-review.yml`의 모델 job은 읽기 권한만 갖는다. 상태 기록·댓글·머지 권한은 별도의 pending/publish job에
있고, 그 job은 기본 브랜치의 결정적 코드만 실행한다. 수동 장 검토 workflow는 별도로 유지한다.

최초 배포 PR은 아직 기본 브랜치에 자동 리뷰 코드가 없어 로컬의 작성자/독립 AI 검토와 원격 CI를 확인한
뒤 적용한다. 이후 main에 필수 검사 ruleset·머지 후 브랜치 삭제를 설정하고 실제 PR로 검증한다.

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
