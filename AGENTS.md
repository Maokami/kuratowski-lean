# 작업 규칙

이 저장소는 쿠라토프스키 정리(유한 그래프가 평면 그래프일 필요충분조건은 `K₅`나 `K₃,₃`의 세분을
갖지 않는 것)를 Lean 4와 Mathlib으로 형식화한다. 쉬운 방향은 끝났고, 어려운 방향을 블루프린트
(`blueprint/src/`)에 따라 형식화하는 중이다. 사람과 AI 에이전트(하위 에이전트 포함)가 모두 이 규칙을
따른다. 문서, 주석, 커밋 메시지는 한국어로 쓴다.

## 빌드와 검사

```sh
lake build                               # 라이브러리와 공리 감사 (KuratowskiAudit.lean)
scripts/blueprint.sh                     # import 목록 검사, lake build, 블루프린트 웹·PDF 판, checkdecls, 전수 검사
scripts/blueprint.sh --quick             # PDF 판과 전수 검사를 뺀 빠른 판
python3 -I scripts/check_definition.py   # 평면성 정의의 전수 검사
```

**Mathlib을 새로 받지 않는다.** `.lake/packages`는 이미 채워져 있다. 새 worktree나 복사본은 같은
Mathlib 버전이 있는 곳에서 APFS clone(`cp -c -R -p`)으로 채우고, `.lake`를 `cp -R`이나 `rsync`로
복사하지 않는다. 패키지를 바꿔야 하면 하나만 갱신한다
(`MATHLIB_NO_CACHE_ON_UPDATE=1 lake update <패키지>`).

## 정책

1. **공리.** 모든 선언은 `propext`, `Classical.choice`, `Quot.sound`만 쓴다. `sorry`, `admit`,
   `axiom` 선언, `native_decide`는 쓰지 않는다. `decide +kernel`은 쓸 수 있다.
   `KuratowskiAudit.lean`이 `Kuratowski` 모듈의 모든 선언을 검사하고, 어기면 `lake build`가 실패한다.
2. **새 파일.** `Kuratowski/`에 파일을 추가하면 `lake exe mk_all --lib Kuratowski`로 `Kuratowski.lean`의
   import 목록(알파벳순)을 다시 만든다. 공리 감사는 루트 모듈이 import하는 모듈만 보고, 빠진 파일은
   빌드되지도 않는다. `scripts/blueprint.sh`가 `mk_all --check`로 확인한다.
3. **블루프린트를 함께 고친다.** 블루프린트 항목에 대응하는 선언을 만들면 같은 변경에서
   - `\planned{...}`를 `\lean{Kuratowski.이름}`(전체 이름)으로 바꾼다.
   - 정리와 보조정리는 진술을 형식화했으면 진술 환경에, 증명까지 끝났으면 증명 환경에도 `\leanok`를
     단다. 정의는 정의 환경 안에 하나만 단다.
   - `\lean`에는 실제로 있는 이름만 넣는다. `checkdecls`가 검사한다.
4. **진술을 맞춘다.** 블루프린트의 자연어 진술과 Lean 진술은 가정, 양화사, 함의 방향이 같아야 한다.
   형식화하다가 진술을 바꿔야 하면 블루프린트도 고친다. 진술을 약하게 바꿔 증명을 쉽게 만들지 않는다.
5. **주황 항목은 블루프린트부터.** `\notready`가 붙은 항목은 형식화하기 전에 블루프린트의 증명을 먼저
   보강한다.
6. **조합적으로 다시 진술한 보조정리는 먼저 전수 검사.** 기하 사실을 회전 체계로 옮긴 새 진술은
   형식화하기 전에 `scripts/check_blueprint.py`에 검사를 추가하고 블루프린트에 `\bfcheck`로 적는다.

## 작성자와 검토자를 나눈다

- 작성자(사람이든 에이전트든)는 스스로 "증명했다"고 선언하지 않는다. 판정은 `lake build`(Lean 커널과
  공리 감사), `checkdecls`, 그리고 작성에 참여하지 않은 검토자가 한다.
- 검토자는 Lean 진술과 블루프린트 진술의 어긋남, 숨은 가정(구조체 필드나 인스턴스 인자로 들어온 조건),
  `\leanok` 표시가 실제와 맞는지를 본다.
- 완료한 변경은 기능 브랜치에 커밋하고 push한 뒤 바로 PR로 올린다. `main`에 직접 push하지 않는다.
  커밋 주소는 이 저장소의 `git config user.email` (GitHub noreply)을 쓴다.
- 머지 정책은 **CI 통과 + 해당 PR head SHA에 대한 AI 리뷰 승인**이다. 자동 머지는 필수 검사와
  최신 base 조건을 우회하지 않는다. 충돌·검사 실패·리뷰 수정 요청은 고친 뒤 새 커밋으로 재검증한다.
- 커밋 제목은 Conventional Commit의 `type(scope): 한국어 설명` 형식을 쓴다.

## 수학적 맥락

- 평면성 정의는 회전 체계로 한다(`Kuratowski/Basic.lean`): 다트 위의 순열 `rot`, 면 순열
  `φ d = rot d.symm`, `IsPlanar G := ∃ R, R.eulerChar = 2 * Nat.card G.ConnectedComponent`.
- 어려운 방향은 Thomassen의 변 수축 증명을 따른다(블루프린트 2장, 경로 A). 형식화 단위는 4–7장,
  설계 결정과 순서는 8장(`blueprint/src/chapters/plan.tex`)에 있다.
- 블루프린트 의존 그래프의 색 (테두리는 진술, 배경은 증명): 초록 = Lean으로 형식화됨, 파랑 = 필요한
  항목이 모두 형식화되어 바로 시작할 수 있음, 주황 테두리 = `\notready`(블루프린트를 먼저 보강).
