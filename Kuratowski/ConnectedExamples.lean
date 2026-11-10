import Kuratowski.Connected

/-!
# Regression examples for the connectivity definitions

Small examples for blueprint definition `def:conn3`; they are the graphs of the `[conn]` check in
`scripts/check_blueprint.py`. Connectivity itself is proved with the structural lemmas
`connectedOn_of_clique` and `not_connectedOn_of_isolated`; kernel computation (`decide`) is used
only for finite adjacency facts and explicit supports.

* The star `K₁,₃` is not 2-connected. Deleting the center empties the support, so we also record
  the pitfall that recomputing the support after deletion makes the pairwise reachability
  condition vacuous.
* A triangle plus an isolated vertex is 2-connected (isolated vertices do not affect
  connectivity).
* `K₄` plus an isolated vertex is 3-connected.
* The path of length 2 is not 2-connected.
* The counterexample graph of blueprint `lem:J2` (edges `01, 12, 20, 30, 31, 34`) is not
  2-connected.
-/

namespace Kuratowski.ConnectedExamples

open SimpleGraph

/-- The simple graph on `Fin n` given by an edge list (only for the examples in this file). -/
def graphOf {n : ℕ} (E : List (Fin n × Fin n)) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ((u, v) ∈ E ∨ (v, u) ∈ E)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

instance {n : ℕ} (E : List (Fin n × Fin n)) : DecidableRel (graphOf E).Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The star `K₁,₃`: center `0` and leaves `1, 2, 3`. -/
abbrev star : SimpleGraph (Fin 4) := graphOf [(0, 1), (0, 2), (0, 3)]

/-- The triangle `012` and an isolated vertex `3`. -/
abbrev triangleIso : SimpleGraph (Fin 4) := graphOf [(0, 1), (1, 2), (0, 2)]

/-- `K₄` on `0, 1, 2, 3` and an isolated vertex `4`. -/
abbrev k4Iso : SimpleGraph (Fin 5) := graphOf [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The path `0 - 1 - 2` of length 2. -/
abbrev path3 : SimpleGraph (Fin 3) := graphOf [(0, 1), (1, 2)]

/-- The counterexample graph of blueprint `lem:J2`: the triangle `012`, a vertex `3` joined to
`0` and `1`, and a leaf `4` joined to `3`. -/
abbrev j2Graph : SimpleGraph (Fin 5) := graphOf [(0, 1), (1, 2), (2, 0), (3, 0), (3, 1), (3, 4)]

/-! ### Examples that are not 2-connected -/

/-- The star is not 2-connected: deleting the center `0` separates leaf `1` from leaf `2`. -/
theorem star_not_twoConnected : ¬ TwoConnected star := by
  refine not_connectedOn_of_isolated star 2 star.support {0} (by simp) (u := 1) (v := 2)
    ⟨(mem_support _).2 ⟨0, by decide⟩, by simp⟩
    ⟨(mem_support _).2 ⟨0, by decide⟩, by simp⟩ (by decide) ?_
  rintro w ⟨h, -, hw⟩
  exact (show ∀ w : Fin 4, ¬ (star.Adj 1 w ∧ w ≠ 0) by decide) w ⟨h, hw⟩

/-- Pitfall: recomputing the support of the star after deleting the center gives the empty set.
On that set the pairwise reachability condition would be vacuous, so `ConnectedOn` removes only the
deleted vertices from the set chosen before deletion. -/
theorem star_deleteVertices_center_support : (deleteVertices star {0}).support = ∅ := by
  ext v
  simp only [mem_support, deleteVertices_adj, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_exists]
  revert v
  decide

/-- The path of length 2 is not 2-connected: deleting the middle vertex `1` separates `0`
from `2`. -/
theorem path3_not_twoConnected : ¬ TwoConnected path3 := by
  refine not_connectedOn_of_isolated path3 2 path3.support {1} (by simp) (u := 0) (v := 2)
    ⟨(mem_support _).2 ⟨1, by decide⟩, by simp⟩
    ⟨(mem_support _).2 ⟨1, by decide⟩, by simp⟩ (by decide) ?_
  rintro w ⟨h, -, hw⟩
  exact (show ∀ w : Fin 3, ¬ (path3.Adj 0 w ∧ w ≠ 1) by decide) w ⟨h, hw⟩

/-- The counterexample graph of `lem:J2` is not 2-connected: deleting `3` separates leaf `4`
from `0`. Hence `lem:J2` is false under the weaker hypothesis that looks only at the support after
deletion. -/
theorem j2Graph_not_twoConnected : ¬ TwoConnected j2Graph := by
  refine not_connectedOn_of_isolated j2Graph 2 j2Graph.support {3} (by simp) (u := 4) (v := 0)
    ⟨(mem_support _).2 ⟨3, by decide⟩, by simp⟩
    ⟨(mem_support _).2 ⟨1, by decide⟩, by simp⟩ (by decide) ?_
  rintro w ⟨h, -, hw⟩
  exact (show ∀ w : Fin 5, ¬ (j2Graph.Adj 4 w ∧ w ≠ 3) by decide) w ⟨h, hw⟩

/-! ### Connected examples (isolated vertices allowed) -/

theorem triangleIso_support : triangleIso.support = ↑({0, 1, 2} : Finset (Fin 4)) := by
  ext v
  rw [mem_support, Finset.mem_coe]
  revert v
  decide

/-- A triangle plus an isolated vertex is 2-connected. -/
theorem triangleIso_twoConnected : TwoConnected triangleIso := by
  refine connectedOn_of_clique _ 2 _ (le_of_eq ?_) ?_
  · rw [triangleIso_support, Set.ncard_coe_finset]
    rfl
  · rw [triangleIso_support]
    intro u hu v hv huv
    exact (show ∀ u v : Fin 4, u ∈ ({0, 1, 2} : Finset (Fin 4)) → v ∈ ({0, 1, 2} : Finset (Fin 4)) →
      u ≠ v → triangleIso.Adj u v by decide) u v hu hv huv

theorem k4Iso_support : k4Iso.support = ↑({0, 1, 2, 3} : Finset (Fin 5)) := by
  ext v
  rw [mem_support, Finset.mem_coe]
  revert v
  decide

/-- `K₄` plus an isolated vertex is 3-connected. -/
theorem k4Iso_threeConnected : ThreeConnected k4Iso := by
  refine connectedOn_of_clique _ 3 _ (le_of_eq ?_) ?_
  · rw [k4Iso_support, Set.ncard_coe_finset]
    rfl
  · rw [k4Iso_support]
    intro u hu v hv huv
    exact (show ∀ u v : Fin 5, u ∈ ({0, 1, 2, 3} : Finset (Fin 5)) →
      v ∈ ({0, 1, 2, 3} : Finset (Fin 5)) → u ≠ v → k4Iso.Adj u v by decide) u v hu hv huv

end Kuratowski.ConnectedExamples
