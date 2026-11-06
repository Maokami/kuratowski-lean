import Kuratowski

/-!
# 공리 감사

`lake build` 때 `Kuratowski` 모듈들(`Kuratowski.lean`과 `Kuratowski/` 아래 파일)에서 선언한
**모든** 상수가 표준 공리 `propext`, `Classical.choice`, `Quot.sound`만 쓰는지 검사한다.
다른 공리가 보이면 오류를 내고 빌드가 실패한다. 이렇게 걸리는 것은 `sorry`(`sorryAx`),
`native_decide`(Lean 4.35에서는 `….native_decide.ax_…` 보조 공리), 새로 선언한 `axiom`과 그것을
간접으로 쓰는 정리다. `decide +kernel`은 공리를 늘리지 않는다.

선언 목록을 손으로 관리하지 않는다. 감사 대상은 루트 모듈 `Kuratowski`가 직접 또는 간접으로
import하는 모듈이므로, `Kuratowski/`에 파일을 추가하면 `Kuratowski.lean`에 import를 추가한다.
-/

open Lean Elab Command

/-- `Kuratowski`로 시작하는 가져온 모듈의 모든 선언이 표준 공리만 쓰는지 검사한다. -/
elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut mods : Nat := 0
  let mut decls : Nat := 0
  let mut used : NameSet := {}
  let mut bad : Array MessageData := #[]
  for i in [:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]!
    unless (`Kuratowski).isPrefixOf mod do continue
    mods := mods + 1
    for c in env.header.moduleData[i]!.constNames do
      decls := decls + 1
      let axs ← collectAxioms c
      used := axs.foldl NameSet.insert used
      let extra := axs.filter (· ∉ allowed)
      unless extra.isEmpty do
        bad := bad.push m!"{c} ({mod}): {extra.toList}"
  if mods == 0 then
    throwError "공리 감사: `Kuratowski` 모듈을 하나도 찾지 못했다"
  unless bad.isEmpty do
    throwError m!"공리 감사 실패: 표준 공리 밖의 공리를 쓰는 선언 {bad.size}개\
      {indentD (MessageData.joinSep bad.toList Format.line)}"
  logInfo m!"공리 감사 통과: 모듈 {mods}개, 선언 {decls}개. 쓰인 공리: {used.toList}"

#audit_axioms

-- 주 정리 (쉬운 방향)
#print axioms Kuratowski.not_isPlanar_of_containsSubdivision
