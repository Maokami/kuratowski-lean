import Kuratowski

/-!
# Axiom audit

During `lake build`, inspect every constant declared in the imported `Kuratowski`
modules. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
An additional axiom, including `sorryAx` or a native-evaluation axiom, fails the build.
`decide +kernel` introduces no additional axiom.

The declaration list comes from the imported module metadata. When adding a library
file, regenerate `Kuratowski.lean` with `lake exe mk_all --lib Kuratowski`; otherwise
that file would be omitted from both the build and this audit.
-/

open Lean Elab Command

/-- Reject nonstandard axioms in every declaration of the imported `Kuratowski` modules. -/
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

-- Both directions and the final equivalence.
#print axioms Kuratowski.not_isPlanar_of_containsSubdivision

#print axioms Kuratowski.isPlanar_of_kuratowskiFree
#print axioms Kuratowski.isPlanar_iff_kuratowskiFree
