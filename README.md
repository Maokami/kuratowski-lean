# 쿠라토프스키 정리 (평면 그래프) — Lean 4 형식화

쿠라토프스키 정리:

> 유한 그래프 `G`가 평면 그래프일 필요충분조건은 `G`가 `K₅`나 `K₃,₃`의 세분(subdivision)을
> 부분 그래프로 갖지 않는 것이다.

이 저장소는 **쉬운 방향**(`K₅`나 `K₃,₃`의 세분을 포함하면 평면 그래프가 아니다)을 완전히
증명한다. 어려운 방향(세분이 없으면 평면 그래프다)은 아직 하지 않았다. 어려운 방향에 쓸 도구 가운데
변 수축 `contractEdge`(`Contract.lean`), 꼭짓점 집합 넓히기 `isPlanar_map_iff`(`Map.lean`),
비고립 꼭짓점이 네 개 이하인 그래프의 평면성(`Small.lean`),
지지 집합 기준의 연결성 정의(`Connected.lean`),
사이클의 순환 꼭짓점 수열 표현(`Cyclic.lean`),
세분의 경로 체계 정의(`Paths.lean`)를 형식화했다. 순환 수열에서 사이클·경로를 만드는 변환과 두 호의
내부 서로소성(`CyclicWalk.lean`), 유한 그래프에서 두 세분 표현의 동치(`PathsSubdivision.lean`,
`SubdivisionOfPaths.lean`), 순환 단어 분류(`CyclicWord.lean`)도 증명했다.

```lean
theorem not_isPlanar_of_containsSubdivision {G : SimpleGraph V} [Finite V] [DecidableEq V]
    (h : ContainsSubdivision G K5 ∨ ContainsSubdivision G K33) : ¬ IsPlanar G
```

`sorry`, `native_decide`, 추가 공리는 쓰지 않았다. `lake build`가 `KuratowskiAudit.lean`으로 모든
선언을 검사해, 쓰인 공리가 표준 공리 `propext`, `Classical.choice`, `Quot.sound`뿐임을 확인한다.

## 증명한 것

| 정리 | 위치 | 내용 |
|---|---|---|
| `not_isPlanar_of_containsSubdivision` | `Subdivision.lean` | **쿠라토프스키 정리, 쉬운 방향** |
| `RotationSystem.eulerChar_le` | `Euler.lean` | 오일러 부등식: 모든 회전 체계에서 `V − E + F ≤ 2c` |
| `IsPlanar.mono` | `Euler.lean` | 평면 그래프의 부분 그래프는 평면 그래프 |
| `IsPlanar.deleteEdge` | `Euler.lean` | 변 하나를 지워도 평면 그래프 |
| `IsPlanar.of_subdivideEdge` | `Smoothing.lean` | 변을 세분한 그래프가 평면이면 원래 그래프도 평면 |
| `K5_not_isPlanar`, `K33_not_isPlanar` | `NonPlanar.lean` | `K₅`, `K₃,₃`는 평면 그래프가 아님 |
| `K5_map_not_isPlanar`, `K33_map_not_isPlanar` | `NonPlanar.lean` | 더 큰 꼭짓점 집합에 넣어도 마찬가지 |
| `IsPlanar.edge_bound` (+ 이분 그래프판) | `NonPlanar.lean` | 차수 1인 꼭짓점이 없으면 `E + 6 + 3I ≤ 3V` (이분: `E + 4 + 2I ≤ 2V`) |
| `K4_isPlanar` | `Planar.lean` | `K₄`는 평면 그래프 (정의가 공허하지 않다는 확인) |
| `IsPlanar.of_iso` | `Iso.lean` | 평면성은 그래프 동형에 대해 불변 |
| `isPlanar_map_iff` | `Map.lean` | 유한한 `W`, `V`와 단사 `f : W ↪ V`에 대해 `K.map f`가 평면 ⇔ `K`가 평면 (고립점 허용) |
| `isPlanar_of_ncard_support_le_four` | `Small.lean` | 유한 그래프의 비고립 꼭짓점이 네 개 이하면 평면 (고립점 수는 제한 없음) |
| `orbitCount_mul_swap_of_sameCycle` / `…_of_not_sameCycle` | `Perm.lean` | 호환을 곱하면 순열의 순환 수가 ±1 바뀜 |

## 정의

### 세분의 경로 체계 (`Paths.lean`)

`SubdivisionPaths K G`는 모든 원래 꼭짓점의 단사 분기점 배치와, 원래 변마다 배치된 두 점을 잇는
Mathlib `Walk`를 묶는다. 각 걸음은 `IsPath`이고 반대 방향은 같은 경로의 역순이다.
내부는 `support`에서 두 끝점을 뺀 `walkInterior`이며, 모든 분기점의 상을 피해야 한다.
서로 다른 **무방향 변**의 내부끼리는 서로소여야 한다. 같은 변을 뒤집은 두 방향은 내부를 공유한다.
고립된 원래 꼭짓점도 배치에 포함한다. `IsSubdivision.exists_subdivisionPaths`는 기존 세분으로부터
분기점 배치가 그대로인 경로 체계를 구성하며 유한성을 요구하지 않는다. 역방향은 `SubdivisionOfPaths.lean`의
`SubdivisionPaths.exists_isSubdivision_le`이며 유한한 꼭짓점 타입 `V`를 가정한다. 합치면
`containsSubdivision_iff_paths`이고 `W`의 유한성은 단사 분기점 배치에서 유도하므로 별도 가정하지 않는다. 무한 완전 그래프의 모든 변을 한 번씩 나누는 경로 체계는
기존 유한 단계의 세분 정의로 표현할 수 없는 예다(이 무한 반례 자체는 Lean으로 형식화하지 않았다).

### 순환 꼭짓점 수열 (`Cyclic.lean`)

`CyclicSequence G m`은 `3 ≤ m`, 단사 `vertex : ZMod m ↪ V`, 모든 위치에서의
`G.Adj (vertex i) (vertex (i + 1))`을 묶는다. 마지막 위치에서 첫 위치로 닫히는 변도 포함하며,
유도 사이클만으로 제한하지 않는다. 시작점을 옮기는 `rotate`와 방향을 뒤집는 `reverse`를 제공한다.
삼각형의 닫는 변과 길이 0·1·2 및 변이 없는 그래프의 배제를 확인했다.
`CyclicWalk.lean`의 `toWalk`는 길이 `m`인 `IsCycle`이고, `arc a b`는 정방향의 `IsPath`다.
호의 길이는 `(b - a).val`이며 `a = b`이면 길이 0이다. 서로 반대 방향의 두 호는 양 끝점을 뺀
내부가 서로소다. 여러 구간을 나누는 성질과 네 위치의 순환 순서 관계는 아직 남아 있다.

### 순환 단어 분류 (`CyclicWord.lean`)

`X`, `Y`, `B`, `-`의 양의 길이 순환 단어에서 `X/B`, `Y/B` 위치가 각각 둘 이상이면 다음 중 하나가
성립한다: 모든 `Y/B`가 연속한 두 `X/B` 사이의 닫힌 호에 있음, `B`가 셋 이상, 또는 두 `Y/B` 위치를
뺀 두 열린 호 각각에 `X/B`가 있음. `classify`가 이 분류를 증명하며 길이 2도 허용한다.
Mathlib의 `sbtw` 열린 호와 실제 사이클 경로의 내부가 같다는 연결도 증명했다.
정규식 `B? X* B? Y*`와 첫 경우의 동치는 아직 Lean으로 형식화하지 않았다.

### 꼭짓점 연결성 (`Connected.lean`)

`ConnectedOn G k A`는 유한한 꼭짓점 타입에서 `k + 1 ≤ A.ncard`이고, `k`개 미만의 점을 지워도
원래 집합 `A`에서 살아남은 점들이 서로 이어진다는 뜻이다. 삭제는 원래 타입에 점을 고립점으로 남긴다.
`TwoConnected G`와 `ThreeConnected G`는 삭제 전의 `G.support`를 기준으로 한다.
삭제 뒤 지지 집합을 다시 계산하면 별 그래프가 잘못 2-연결로 판정될 수 있어 그렇게 하지 않는다.
`k = 0`에서는 크기 조건만 남는다. 별·경로의 음성 예와 고립점을 더한 삼각형·`K₄`의 양성 예를
`ConnectedExamples.lean`에서 커널로 확인한다. 수축 가능한 변의 존재 정리는 아직 형식화하지 않았다.

### 평면성 (`Basic.lean`)

위상적 정의(ℝ²로의 매장)를 쓰려면 조르당 곡선 정리가 필요한데 Mathlib에 없다. 그래서 위상
그래프 이론의 표준 조합적 정의를 쓴다 (Mohar–Thomassen, *Graphs on Surfaces*, 3장).

- **회전 체계** `RotationSystem G`: 다트(방향 있는 변) 위의 순열 `rot`. 다트의 시작점을
  보존하고, 한 꼭짓점의 다트들은 `rot`의 한 순환을 이룬다. 즉 각 꼭짓점 둘레의 이웃 순서다.
- **면**: 면 순열 `φ d = rot (d.symm)`의 순환. 고립점은 면 하나로 센다.
- **평면성** `IsPlanar G`: `V − E + F = 2 · (연결 성분 수)`인 회전 체계가 있다.

오일러 부등식(`eulerChar_le`)에 따라 각 성분에서 `V − E + F ≤ 2`이므로, 이 등식은 "모든 성분이
종수 0인 곡면, 즉 구면에 매장된다"는 뜻이다. 회전 체계와 곡면 매장의 대응 자체
(Heffter–Edmonds–Ringel)는 위상수학의 정리이며 여기서 형식화하지 않았다.

개수는 모두 `Nat.card`와 `Set.ncard`로 센다. 그래서 정의가 `Fintype`이나 `DecidableRel`
인스턴스에 의존하지 않는다.

### 세분 (`Subdivision.lean`)

`IsSubdivision K f H`: `K`(꼭짓점 `W`)를 `f : W ↪ V`로 `V`에 놓은 `K.map f`에서 시작한다.
그 뒤 변 `xy`를 아직 쓰이지 않은 꼭짓점 `w`로 나누는 일(`subdivideEdge`)을 반복해 `H`를
얻는다. `ContainsSubdivision G K`는 그런 `H`가 `G`의 부분 그래프라는 뜻이다. 이는 `K`가 `G`의
위상 소수(topological minor)라는 것과 같다 (Diestel, *Graph Theory*, 1.7절).

## 증명 구조

모든 단계가 하나의 사실로 귀결된다. 순열에 호환 `swap a b`를 곱하면, `a`와 `b`가 같은
순환에 있을 때는 그 순환이 갈라지고 (+1), 다른 순환에 있을 때는 두 순환이 합쳐진다 (−1)
(`Perm.lean`).

1. **변 지우기** (`Deletion.lean`): 다트 `d`의 변을 지운 그래프의 면 순열은
   `φ * swap d d.symm`에서 `d`, `d.symm`을 잘라 낸 것이다. 그래서 `d`, `d.symm`이 같은 면에
   있으면 `F`가 1 늘고, 다른 면에 있으면 1 준다. 후자에서는 `d`의 면을 따라 돌면 지운 변을 쓰지
   않는 길이 생기므로, 그 변은 다리가 아니다.
2. **오일러 부등식, 부분 그래프** (`Euler.lean`): 1에 연결 성분 수 세기(`Components.lean`)를
   더해 변의 수에 대한 귀납법으로 증명한다.
3. **세분 되돌리기** (`Smoothing.lean`): 꼭짓점 `w`의 두 다트를 면 순열에서 잘라 내면,
   `x → w → y`로 돌던 면이 `x → y`로 바로 간다. `F`는 그대로이고 `w`가 고립점이 되면서 면과
   성분이 하나씩 는다.
4. **마무리** (`NonPlanar.lean`, `Subdivision.lean`): `G`가 평면이면 세분 `H ≤ G`도 평면이고(2),
   세분을 되돌린 `K.map f`도 평면이다(3). 그런데 `K₅.map f`는 면이 모두 길이 3 이상이라
   `3F ≤ 2E`가 되어 오일러 공식과 모순이다. `K₃,₃.map f`는 이분 그래프라 면이 모두 길이 4 이상이고,
   같은 방식으로 모순이 나온다.

## 정의 검증

- `scripts/check_definition.py`: 같은 평면성 정의를 파이썬으로 옮겨 작은 그래프에서 전수 검사한다.
  꼭짓점 1–5개인 그래프 1,099개 중 정의상 비평면은 `K₅` 하나뿐이다. Petersen 그래프,
  세분된 `K₃,₃`, `K₅ ⊔ K₄`는 비평면, 정팔면체·정육면체·`K₅ − e`·`K₃,₃ − e`는 평면으로
  판정되어 알려진 결과와 모두 일치한다.
- 정의와 정리 문장은 별도 리뷰를 두 차례 거쳤다. 두 번째 리뷰에서 세분 정의가 표준적인 위상 소수
  정의와 같은지 따로 확인했다.

```sh
python3 -I scripts/check_definition.py
```

## 남은 일: 어려운 방향

`K₅`, `K₃,₃`의 세분이 없는 그래프에 대해 평면 회전 체계를 실제로 만들어야 한다. Thomassen의
변 수축 증명을 따른다. 먼저 최소 반례가 3-연결임을 보이고, 3-연결 그래프는 변을 수축해
귀납하며, 볼록 매장 대신 회전 체계로 면을 다시 짠다.

설계는 [leanblueprint](https://github.com/PatrickMassot/leanblueprint) 형식의 블루프린트
`blueprint/src/`에 있다. 경로 비교(2장), 형식화한 쉬운 방향(3장), 어려운 방향의 형식화 단위(4–7장),
설계 결정과 진행 순서(8장)로 이루어진다. 각 항목에 Lean 선언, 의존 관계(`\uses`), 진행 상태
(`\leanok`, `\notready`)가 붙어 있고, 이것으로 진행 상태가 색칠된 의존 그래프가 만들어진다.
기하를 조합적으로 다시 진술한 보조정리는 형식화하기 전에 `scripts/check_blueprint.py`로 작은
그래프에서 먼저 검사했다.

## 블루프린트 빌드

`leanblueprint`(`uv tool install leanblueprint`), TeX Live(xelatex, kotex), graphviz가 필요하다.
`uv tool`은 `leanblueprint`만 `PATH`에 올려서 같은 가상환경의 `plastex`가 보이지 않는데,
`scripts/blueprint.sh`가 그 경로와 TeX Live의 `bin`을 `PATH` 앞에 넣고 실행한다.

```sh
scripts/blueprint.sh          # import 검사 → lake build(공리 감사) → 웹·PDF 판 → checkdecls → 전수 검사
scripts/blueprint.sh --quick  # PDF 판과 전수 검사를 건너뛴다
scripts/blueprint.sh serve    # 만든 웹 판을 http://127.0.0.1:8000 에서 본다
```

웹 판은 `blueprint/web/`(의존 그래프는 `dep_graph_document.html`), PDF 판은 `blueprint/print/print.pdf`에
생긴다. `checkdecls`는 블루프린트의 `\lean{...}` 이름이 Lean에 모두 있는지 확인하고, 전수 검사는
`scripts/check_blueprint.py`로 새 보조정리 진술을 작은 그래프에서 확인한다.

`checkdecls`를 위해 `lakefile.toml`에 [checkdecls](https://github.com/PatrickMassot/checkdecls)
의존성을 넣었다. 아직 Lean 선언이 없는 항목은 `\lean` 대신 `\planned{...}`로 예정 이름을 적는다.
`\lean`에 넣으면 `checkdecls`가 실패하기 때문이다. GitHub 원격 저장소가 아직 없어 `\github`,
`\home`, `\dochome`은 비워 두었다 (Lean 링크는 API 문서가 생기면 동작한다).

## 빌드

Lean `v4.35.0`, Mathlib `v4.35.0`.

```sh
lake build   # 라이브러리와 공리 감사 (KuratowskiAudit.lean)
```

공리 감사는 `Kuratowski` 모듈의 모든 선언이 `propext`, `Classical.choice`, `Quot.sound`만 쓰는지
검사한다. `sorry`, `native_decide`, 새 `axiom`이 들어오면 `lake build`가 실패한다. 선언 목록을 따로
관리하지 않는다. 새 파일은 `lake exe mk_all --lib Kuratowski`로 `Kuratowski.lean`의 import 목록에
넣으면 감사 대상이 되고, `scripts/blueprint.sh`가 빠진 파일이 없는지 `mk_all --check`로 확인한다.
작업 규칙은 `AGENTS.md`에 있다.

수동 Claude Action 검토의 설정·비용·검증 한계는 [Continuous AI 실험](docs/continuous-ai.md)에 있다.

`.lake/packages`는 같은 Mathlib 버전을 쓰는 `~/projects/ctic-lean`에서 APFS clone으로
채웠다 (`cp -c -R -p`, 추가 디스크 사용 거의 없음). `checkdecls`만 따로 받았다
(`MATHLIB_NO_CACHE_ON_UPDATE=1 lake update checkdecls`; 다른 패키지의 리비전은 그대로다).

## 파일

| 파일 | 내용 |
|---|---|
| `Perm.lean` | 순환 수 `orbitCount`, 호환 보조정리, 잘라 내기 `cut` |
| `Basic.lean` | 회전 체계, 면, 오일러 지표, `IsPlanar` |
| `Components.lean` | 연결 성분·고립점·변 수 세기 (변 지우기, 세분, `K.map f`) |
| `Contract.lean` | 변 수축 `contractEdge`와 국소 성질 (어려운 방향용 정의) |
| `Deletion.lean` | 변 지우기 수술과 면 수 공식 |
| `Euler.lean` | 오일러 부등식, 부분 그래프 |
| `Smoothing.lean` | 세분 되돌리기 |
| `NonPlanar.lean` | 변 개수 상한, `K₅`·`K₃,₃` 비평면성 |
| `Subdivision.lean` | 세분 정의, 쿠라토프스키 정리(쉬운 방향) |
| `Planar.lean` | `K₄` 평면성 |
| `Iso.lean` | 동형 불변성 |
| `Map.lean` | 꼭짓점 집합 넓히기: 다트 대응, 회전 체계 옮기기, 고립점·성분 수 |
| `Small.lean` | 비고립 꼭짓점이 네 개 이하인 그래프의 평면성 |
| `Connected.lean` | 원래 지지 집합 기준의 꼭짓점 삭제·연결성·2-연결·3-연결 정의 |
| `ConnectedExamples.lean` | 별·경로·고립점을 더한 완전 그래프·J2 반례로 연결성 정의 확인 |
| `Cyclic.lean` | `ZMod`로 인덱싱한 단사 사이클 수열, 회전·역순과 경계 예제 |
| `CyclicWalk.lean` | 순환 수열에서 Mathlib 사이클·호 경로 구성, 두 방향 호의 내부 서로소성 |
| `Paths.lean` | 세분의 경로 체계와 내부 꼭짓점 조건 |
| `PathsSubdivision.lean` | 기존 세분에서 분기점 배치를 보존하는 경로 체계 구성 |
| `SubdivisionOfPaths.lean` | 유한 그래프에서 경로 체계로 세분을 구성하고 두 표현의 동치 증명 |
| `CyclicWord.lean` | 네 글자 순환 단어의 구간·공통 위치 셋·교대 배치 분류 |
| `PathsExamples.lean` | 실제 내부 꼭짓점을 갖는 경로 체계와 조건 위반 후보 예제 |

| 그 밖의 파일 | 내용 |
|---|---|
| `KuratowskiAudit.lean` | 공리 감사 (`lake build` 때 모든 선언 검사) |
| `AGENTS.md`, `CLAUDE.md` | 사람·에이전트 공통 작업 규칙 (`CLAUDE.md`는 `AGENTS.md`를 가져온다) |
| `scripts/blueprint.sh` | 블루프린트 빌드와 검사를 한 번에 |
| `blueprint/src/content.tex` | 블루프린트 본문 (장별 파일은 `blueprint/src/chapters/`) |
| `blueprint/src/macros/common.tex` | 한국어 정리 이름, `\planned`, `\bfcheck` 매크로 |
| `blueprint/src/web.tex`, `print.tex` | 웹 판(plasTeX)과 PDF 판(xelatex, kotex)의 머리말 |
| `blueprint/src/plastex.cfg`, `terms-ko.xml` | plasTeX 설정, 웹 판의 "증명" 표기 |
| `scripts/check_definition.py` | 평면성 정의의 전수 검사 |
| `scripts/check_blueprint.py` | 블루프린트 새 보조정리 진술의 전수 검사 |
