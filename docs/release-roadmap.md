# 증명 릴리스와 Continuous AI 재사용 계획

사용자 승인: 2026-11-10. 아래 순서로 작은 PR을 검증하고 반영한다.
최종 정리의 뜻과 공리 기준은 유지한다. Lean 주석은 명확하고 간결한 영어·수식으로 정리한다.

## 1. 재사용 가능한 Lean 라이브러리

- [x] 일반 순열, 회전의 이웃 열거, 수축 사상, 순환 수열 API를 기초 모듈로 옮긴다.
- [x] 중복 증명을 공통 정리로 대체하고 불필요한 가정·경고 억제를 검토한다.
- [x] Lean 주석과 docstring을 영어로 정리하고 코드 토큰 불변 또는 명시한 API 변경을 확인한다.
- [x] 모듈 안내와 Mathlib 기여 후보 목록을 만든다. upstream 제출은 별도의 사람 검토 과정이다.

## 2. Kuratowski 릴리스

- [x] 공개 범위, 라이선스·저자·인용, 변경 기록과 사용 예제를 정리한다.
- [x] 외부 Lake 소비 프로젝트에서 고정 커밋으로 import와 최종 정리 적용을 확인한다.
- [x] 전체 빌드, 새 공리 감사, import 목록, 블루프린트 웹·PDF·선언 검사와 유한 검사를 통과한다.
- [x] 정확한 PR head의 CI와 독립 리뷰 뒤 v1.0.0 태그·PDF·HTML·검증 기록을 게시했다.

범위는 유한 단순 그래프의 조합적 평면성이다. 회전 체계와 위상적 매장의 대응은 이 릴리스에 포함하지 않는다.

## 3. Continuous AI 독립 패키지

- [x] Kuratowski의 조사·검증·게시와 Smarandache–Wellin의 PR 보고·분류에서 공통 기능을 추렸다.
- [x] continuous-ai-kit에 재사용 workflow, version 1 설정, 시험, 설치·복구 문서를 묶었다.
- [x] Lean 검사와 저장소별 머지 정책을 공통 코드와 분리했다.
- [x] Kuratowski Lean 조사와 작은 비-Lean 예제에서 재사용 workflow의 실제 실행을 검증했다.
- [x] 인증 값은 소비 저장소에 두고, 설치·갱신은 검토 가능한 PR로 제공했다.
- [ ] Smarandache–Wellin의 draft PR #13은 사람 승인·머지 후 실제 workflow를 검증한다.

SW는 실제 GitHub 자료 수집·기존 보고서 호환·오래된 결과 거부까지 확인했다. 그 저장소의
`AGENTS.md`는 에이전트의 자기 PR 머지를 금지하므로 배포 완료로 표시하지 않는다.

## 4. gh-aw 비교

- [x] 첫 Claude Action 실행의 소스·plan·prompt·schema를 고정한 gh-aw 수동 실험을 구성했다.
- [x] gh-aw v1.0.1 compile과 입력 파일 재현, 생성 YAML의 권한·오류 보고 설정을 검토했다.
- [ ] 별도 API 인증을 준비한 뒤 제한된 수동 실행으로 비교한다.
- [ ] 유효한 결과, 검토 부담, 실패 복구, 유지할 코드와 비용 근거를 기록하고 구현을 선택한다.

일반 엔진 프레임워크나 새로운 workflow 언어를 만들지 않는다. 모델 추정 비용과 실제 청구액을 구분한다.
gh-aw 실행에 필요한 인증이 없으면 실행된 것처럼 보고하지 않는다.

[설치와 운영 안내](https://github.com/Maokami/continuous-ai-kit)와
[실측 성공·실패 기록](https://github.com/Maokami/continuous-ai-kit/blob/main/docs/adoption-evidence.md)은
독립 패키지에서 관리한다. 현재 두 레인은 Claude Action 기반이며 gh-aw는 미실행 비교안이다.
