import Kuratowski.SplitVertex

/-!
# Face boundaries do not repeat vertices (blueprint `lem:J1`)

For a genus-0 rotation system of a 2-connected graph, distinct darts on one face have distinct
start vertices (`RotationSystem.eq_of_sameCycle_facePerm_of_fst_eq`). Suppose two darts `d ≠ e`
with the same start vertex `w` lie on one face. Their predecessors `φ⁻¹ d` and `φ⁻¹ e` are two
distinct darts of that face entering `w`. Splitting `w` at these two corners (`SplitVertex.lean`)
increases `χ` by 2. By 2-connectivity the start vertices of the predecessors `φ⁻¹ d`, `φ⁻¹ e`
stay connected after deleting `w`, so the linking condition holds and the number of components is
unchanged. This
contradicts Euler's inequality. We use the predecessors because `d.symm` and `e.symm` need not lie
on the same face.
-/

namespace Kuratowski

open SimpleGraph Equiv Equiv.Perm

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

variable [Finite V] [DecidableEq V]

/-- Blueprint `lem:J1`: for a genus-0 rotation system of a 2-connected graph, distinct darts on
one face have distinct start vertices. If two darts `d ≠ e` with the same start vertex `w` lie on
one face, their predecessors `φ⁻¹ d` and `φ⁻¹ e` enter `w` along that face. Splitting `w` at these
two corners satisfies the linking condition by 2-connectivity, contradicting Euler's inequality
(`not_splitLinked_of_eulerChar`). -/
theorem eq_of_sameCycle_facePerm_of_fst_eq (hG : TwoConnected G) (R : RotationSystem G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) {d e : G.Dart}
    (h : R.facePerm.SameCycle d e) (hfst : d.fst = e.fst) : d = e := by
  by_contra hde
  set e₁ := R.facePerm⁻¹ d with he₁
  set e₂ := R.facePerm⁻¹ e with he₂
  have hd : R.facePerm e₁ = d := by simp [he₁]
  have he : R.facePerm e₂ = e := by simp [he₂]
  have hsnd : e₁.snd = e₂.snd := by
    rw [← R.facePerm_fst e₁, ← R.facePerm_fst e₂, hd, he, hfst]
  have hne : e₁ ≠ e₂ := fun h' ↦ hde (by rw [← hd, ← he, h'])
  have hface : R.facePerm.SameCycle e₁ e₂ := by
    have h' := h
    rw [← hd, ← he, sameCycle_apply_left, sameCycle_apply_right] at h'
    exact h'
  apply not_splitLinked_of_eulerChar hR hsnd hne hface
  refine ⟨e₁.symm, e₂.symm, hsnd, symm_not_mem_splitSet hsnd hne, symm_mem_splitSet, ?_⟩
  -- 2-connectivity: the start vertices of `e₁` and `e₂` stay connected after deleting `w`
  have hw1 : e₁.fst ≠ e₂.snd := fun h' ↦ e₁.adj.ne (h'.trans hsnd.symm)
  have hw2 : e₂.fst ≠ e₂.snd := e₂.adj.ne
  exact hG.2 {e₂.snd} (by rw [Set.ncard_singleton]; omega) e₁.fst
    ⟨e₁.adj.mem_support_left, fun h' ↦ hw1 (Set.mem_singleton_iff.1 h')⟩ e₂.fst
    ⟨e₂.adj.mem_support_left, fun h' ↦ hw2 (Set.mem_singleton_iff.1 h')⟩

end RotationSystem

end Kuratowski
