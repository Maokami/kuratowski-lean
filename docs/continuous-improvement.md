# Lean 코드의 지속적인 개선 자동화 검토

2026-11-10에 저장소의 workflow와 아래 공식 문서를 확인한 설계안이다.
새 workflow를 설치하거나 예약 실행·모델 과금을 활성화한 결과는 아니다.
로컬에는 gh-aw v1.0.1이 설치되어 있고, 저장소 secret 이름 조회에서는
`CLAUDE_CODE_OAUTH_TOKEN`만 확인했다(값은 읽지 않음). 최신 문서와 설치 버전의 옵션 차이는
실제 도입 시 고정한 버전으로 compile·수동 실행해 확인해야 하며, 이번 검토에서는 실행하지 않았다.

이후 첫 운영 단계로 Claude Action 기반 `lean-improvement.yml`을 추가했다.
[현재 운영 범위와 실행 방법](continuous-ai.md#정기-개선-후보-조사-첫-운영-단계)을 참고한다.
아래 내용은 최종 폐루프에 대한 설계이며, 자동 수정·PR 생성·gh-aw 비교 실행은 후속 단계다.

## 판단

gh-aw를 **개선 후보 발견과 작은 PR 제안**에 한정해 시험할 가치가 있다.
기존 Claude Action 기반 PR 리뷰·CI·머지는 유지하고, 그 앞에 개선 작업을 찾는 레인을 추가한다.
기존 Claude 구독 활용이 우선이면 같은 레인을 Claude Action으로도 구현할 수 있다.
Continuous AI는 이런 반복 작업을 자동화하는 개념이고 gh-aw는 이를 구현하는 도구 중 하나다.

현재 `pr-review.yml`은 PR 생성 후 검토·머지를 처리하고, `lean-blueprint-review.yml`은 사람이 장을
선택해 수동 실행하고 Claude가 작성한 검토 보고서를 artifact로 남긴다.
정기적인 코드 품질 탐색과 개선 PR 작성은 없다.
따라서 기존 PR 리뷰를 gh-aw로 교체하는 것보다 **탐색 → 제안 → 검증 → PR**을 추가하는 것이 목적에 맞다.
GitHub Next의 Duplicate Code Detector도 주기적으로 중복을 찾아 이슈를 제안하는 공식 예제다.
Lean의 의미·가정·공리 제약은 이 저장소에 맞게 따로 지정해야 한다.

## 제안 흐름

```text
주 1회 또는 수동 실행
  → 최신 main SHA와 열린 개선 이슈/PR 확인
  → 변경 모듈 또는 순환 배정한 작은 모듈 묶음 조사
  → 근거가 있는 후보 최대 3개, 실익이 없으면 no-op
  → 후보 1개를 선택해 작은 변경
  → Lean 빌드·공리 감사·import·블루프린트 선언 검사
  → PR 최대 1개
  → 기존의 독립 AI 리뷰 + 해당 head의 Lean CI
  → 현재 저장소 정책에 따라 머지
```

탐색 대상은 중복 증명, 불필요한 가정, 기초 API의 상위 모듈 의존, 취약한 증명 자동화,
문서와 진술 불일치다. 단순 줄 수 감소를 성과로 삼지 않는다.

초기 작성 범위는 정리 진술과 공개 이름을 보존하는 증명 본문 개선으로 제한한다.
가정 변경, 정의 변경, 모듈 이동, toolchain·의존성·공리 감사·workflow 변경은 후보 보고로 남긴다.
이번 세분 구성 정리의 모듈 이동도 사람이 승인한 개선으로, 초기 자동 작성 범위에는 포함하지 않는다.
개선 전후의 선언 타입, 변경 이유, 실행한 검사와 실패 로그를 PR에 기록한다.
컴파일은 해당 진술의 증명을 확인하므로, 의도와 다른 진술로 바뀌지 않았는지도 별도로 검토한다.

같은 후보는 파일 경로·선언 이름·개선 종류로 식별한다. 열린 대응 PR이 있으면 생성을 건너뛴다.
실패한 후보의 SHA·이유·재시도 횟수를 기록하고, 소스나 실패 원인이 바뀌기 전에는 반복하지 않는다.
열린 자동 개선 PR은 최대 1개, 동일 후보의 자동 수정 재시도는 최대 1회로 제안한다.
소스 SHA·검토 범위·정책이 모두 같고 이미 검토를 끝낸 묶음이면 비싼 빌드·추론을 건너뛴다.
전체 점검은 별도 수동 실행으로 가능하게 한다.

## Claude Action과 gh-aw의 선택

| 항목 | 기존 Claude Action 확장 | gh-aw 신규 개선 레인 |
| --- | --- | --- |
| 정기 조사·코드 수정·PR | Actions와 추가 구현으로 가능 | workflow와 safe-outputs로 구성 |
| 기존 구독 토큰 | 현재 저장소에서 사용 중 | Claude 구독 OAuth 미지원 |
| 결과 반영 | 검증·게시 job을 직접 구현 | 읽기 에이전트와 쓰기 safe-output 단계 분리 |
| 엔진 비교·네트워크·비용 정책 | 별도 구성 | 프레임워크의 공통 구조 사용 |
| Lean 검증 | 직접 구성 | 직접 구성; 프레임워크가 Lean 진술을 판단해주지는 않음 |

이 저장소의 당장 비용은 기존 구독 경로가 유리할 수 있다. 단 개인 작업과 사용 한도를 공유한다.
gh-aw는 선택한 모델의 추론 비용과 GitHub Actions 자원을 사용한다.
Anthropic API/WIF 또는 Copilot 추론 등 별도 인증 경로가 필요하며, 모델·사용량 없이 월 비용을
확정할 수 없다. 개인 저장소의 Copilot은 보통 `COPILOT_GITHUB_TOKEN`을 쓰는 경로를 검토하고,
조직 중앙 과금용 `copilot-requests: write`를 개인 저장소에 그대로 적용하지 않는다.
모델 인증과 PR 생성·CI 트리거 인증은 별개다.

gh-aw 시험은 수동 실행과 `safe-outputs.staged: true`로 시작해 쓰기 결과를 미리 본다.
턴·시간·실행당/일일 AI Credits 제한을 설정하고, 작은 범위의 2회 실행에서 실제 사용량을 측정한 뒤
주기를 정한다. AI Credits 제한을 공급자 청구액의 엄밀한 상한으로 간주하지 않는다.
Lean/mathlib 다운로드와 컴파일 자원도 별도 비용이며 같은 lockfile의 캐시를 재사용한다.
캐시 복원 뒤에도 현재 소스의 공리 감사와 빌드는 실행한다.

## 이 저장소에 연결하기 전에 해결할 점

1. **모델 인증:** 현재 Claude 구독 토큰은 gh-aw에 재사용할 수 없다.
   사용할 Copilot 계정 또는 API 과금 경로와 사용 상한을 정해야 한다.
2. **CI 트리거:** 기본 `GITHUB_TOKEN`으로 만든 PR은 후속 CI와 PR 리뷰를 시작하지 않을 수 있다.
   공식 문서의 GitHub App/PAT 기반 CI 트리거 또는 PR 작업용 인증을 구성하고 실제 head에서 검증한다.
   현재 CI 검증기는 `ci.yml`의 `pull_request` 실행과 정확한 head SHA를 요구한다.
   `ci.yml`에는 dispatch가 없으므로 임의 수동 CI 실행을 대체 증거로 쓸 수 없다.
   CI를 깨우는 추가 커밋만 PAT로 쓰면 PR 작성자는 여전히 봇일 수 있다.
3. **봇 신원:** 현재 PR 리뷰는 OWNER/MEMBER/COLLABORATOR의 같은 저장소 PR 중
   열려 있고 draft가 아니며 base가 main인 경우만 처리한다.
   봇 PR의 실제 `author_association`을 확인해야 하며, 모든 봇을 허용하면 안 된다.
   전용 App의 설치·신원·저장소·신뢰한 실행과 생성 SHA/PR의 연결을 검증하는 별도 정책이 필요하다.
4. **권한 분리:** 수정·빌드하는 작성 에이전트와 리뷰 에이전트를 분리한다.
   게시용 자격증명은 safe-output 단계에만 주고, 테스트할 코드와 함께 실행하지 않는다.
5. **캐시·네트워크:** Lean 설치, lockfile에 맞는 mathlib 캐시, Lake 빌드가 선택한 샌드박스의
   네트워크 허용 목록에서 실제로 동작하는지 확인한다. 성공 전에는 자동 주기를 켜지 않는다.

## 도입 순서와 성공 기준

- 1단계: 수동·staged 조사만으로 이번에 찾은 중복 증명과 비슷한 수준의 후보를 근거와 함께 찾는지 확인.
- 2단계: 진술 보존 변경 1건을 PR로 만들고 CI·독립 리뷰·현재 SHA 지정 머지·브랜치 정리까지 확인.
- 3단계: 주 1회로 예약. 주기별 유지할 가치가 있는 후보가 적으면 빈도를 낮추거나 중단.

원하는 평가는 후보의 정확성, 실제 채택된 개선, 검토 부담, 실패/중복 비율, 실행당 사용량이다.
이 설계가 검증되기 전에는 기존 PR 리뷰와 머지를 gh-aw로 전환할 이유가 없다.

## 공식 근거

- [Continuous AI의 개념](https://githubnext.com/projects/continuous-ai/)
- [GitHub Agentic Workflows와 예제](https://github.github.com/gh-aw/)
- [Duplicate Code Detector](https://github.com/githubnext/agentics/blob/main/docs/duplicate-code-detector.md)
- [Claude Action의 정기 작업과 구독 인증](https://code.claude.com/docs/en/github-actions)
- [gh-aw Claude 엔진과 구독 OAuth 제한](https://github.github.com/gh-aw/reference/engines/claude/)
- [gh-aw 모델 인증과 GitHub 작업 인증](https://github.github.com/gh-aw/reference/auth/)
- [safe-outputs와 staged 모드](https://github.github.com/gh-aw/reference/safe-outputs/)
- [봇 PR의 CI 트리거](https://github.github.com/gh-aw/reference/triggering-ci/)
- [실행 비용과 제한](https://github.github.com/gh-aw/reference/cost-management/)
