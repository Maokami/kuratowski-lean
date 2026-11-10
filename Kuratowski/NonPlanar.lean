import Kuratowski.Basic
import Kuratowski.Components

/-!
# Edge bounds and non-planarity of `K₅` and `K₃,₃`

Without vertices of degree 1, every face cycle has length at least 3 (at least 4 for bipartite
graphs), so the number of face cycles is bounded above by the number of edges. (Such a vertex can
give a face of length 2, as in `K₂`.) Combining Euler's formula `V - E + F = 2c` with "each
isolated vertex is a component, and an edge gives one more component" (`c ≥ I + 1`), a planar
graph with at least one edge and no vertex of degree 1 satisfies

* `E + 6 + 3I ≤ 3V`
* `E + 4 + 2I ≤ 2V` if it is bipartite

where `I` is the number of isolated vertices. Isolated vertices are allowed so that the bounds
apply directly to `K₅` and `K₃,₃` placed in a larger vertex set (`K.map f`). `K₅` has
`V - I = 5` and `E = 10`, violating the first bound; `K₃,₃` has `V - I = 6` and `E = 9`, violating
the second.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- No vertex of degree 1: for each edge `uv`, the end `v` has a neighbor other than `u`. -/
def NoLeaf (G : SimpleGraph V) : Prop := ∀ u v, G.Adj u v → ∃ z, G.Adj v z ∧ z ≠ u

namespace RotationSystem

variable (R : RotationSystem G)

/-- Without vertices of degree 1 every face cycle has length at least 3, so `3O ≤ 2E`, where
`O = orbitCount R.facePerm` counts face cycles (faces at isolated vertices are not included). -/
lemma three_mul_orbitCount_le [Finite V] (h : NoLeaf G) :
    3 * orbitCount R.facePerm ≤ 2 * G.edgeSet.ncard := by
  rw [← card_dart_eq]
  refine mul_orbitCount_le R.facePerm 3 fun d k hk hk3 => ?_
  obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
  · simpa using R.facePerm_ne_self d
  · obtain ⟨z, hz, hne⟩ := h _ _ d.adj
    rw [pow_two, Equiv.Perm.mul_apply]
    exact R.facePerm_facePerm_ne_self d hz hne

private lemma fin_two_triangle : ∀ a b c : Fin 2, a ≠ b → b ≠ c → c ≠ a → False := by decide

/-- In a bipartite graph the two colors alternate along a face, so no face has length 3. -/
lemma facePerm_pow_three_ne_self (hbip : G.IsBipartite) (d : G.Dart) :
    (R.facePerm ^ 3) d ≠ d := by
  obtain ⟨C⟩ := hbip
  intro h
  have h3 : (R.facePerm (R.facePerm d)).snd = d.fst := by
    have := congrArg (fun x : G.Dart => x.fst) h
    simpa [pow_succ, Equiv.Perm.mul_apply, -facePerm_apply] using this
  have e1 := C.valid d.adj
  have e2 := C.valid (R.facePerm d).adj
  have e3 := C.valid (R.facePerm (R.facePerm d)).adj
  simp only [facePerm_fst] at e2 e3
  rw [h3] at e3
  exact fin_two_triangle _ _ _ e1 e2 e3

/-- In a bipartite graph without vertices of degree 1 every face cycle has length at least 4,
so `4O ≤ 2E`, where `O = orbitCount R.facePerm` (faces at isolated vertices are not included). -/
lemma four_mul_orbitCount_le [Finite V] (h : NoLeaf G) (hbip : G.IsBipartite) :
    4 * orbitCount R.facePerm ≤ 2 * G.edgeSet.ncard := by
  rw [← card_dart_eq]
  refine mul_orbitCount_le R.facePerm 4 fun d k hk hk4 => ?_
  obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  · simpa using R.facePerm_ne_self d
  · obtain ⟨z, hz, hne⟩ := h _ _ d.adj
    rw [pow_two, Equiv.Perm.mul_apply]
    exact R.facePerm_facePerm_ne_self d hz hne
  · exact R.facePerm_pow_three_ne_self hbip d

end RotationSystem

variable [Finite V]

/-- A planar graph with an edge and no vertex of degree 1 satisfies `E + 6 + 3I ≤ 3V`, where `I`
is the number of isolated vertices. Without isolated vertices this is the familiar
`E ≤ 3V - 6`. -/
theorem IsPlanar.edge_bound (hP : IsPlanar G) (h : NoLeaf G) {u v : V} (huv : G.Adj u v) :
    G.edgeSet.ncard + 6 + 3 * {w | G.IsIsolated w}.ncard ≤ 3 * Nat.card V := by
  obtain ⟨R, hR⟩ := hP
  have hF := R.three_mul_orbitCount_le h
  have hc := ncard_isolated_add_one_le G huv
  unfold RotationSystem.eulerChar RotationSystem.numFaces at hR
  push_cast at hR
  omega

/-- A bipartite planar graph with an edge and no vertex of degree 1 satisfies
`E + 4 + 2I ≤ 2V`. Without isolated vertices this is the familiar `E ≤ 2V - 4`. -/
theorem IsPlanar.edge_bound_of_isBipartite (hP : IsPlanar G) (h : NoLeaf G)
    (hbip : G.IsBipartite) {u v : V} (huv : G.Adj u v) :
    G.edgeSet.ncard + 4 + 2 * {w | G.IsIsolated w}.ncard ≤ 2 * Nat.card V := by
  obtain ⟨R, hR⟩ := hP
  have hF := R.four_mul_orbitCount_le h hbip
  have hc := ncard_isolated_add_one_le G huv
  unfold RotationSystem.eulerChar RotationSystem.numFaces at hR
  push_cast at hR
  omega

/-! ## The graph `K.map f` on a larger vertex set -/

section Map

variable {W : Type*} [Finite W] {K : SimpleGraph W} (f : W ↪ V)

omit [Finite V] [Finite W] in
lemma NoLeaf.map (h : NoLeaf K) : NoLeaf (K.map f) := by
  intro u v huv
  obtain ⟨a, b, hab, rfl, rfl⟩ := (map_adj f K u v).1 huv
  obtain ⟨z, hz, hne⟩ := h a b hab
  exact ⟨f z, (map_adj f K _ _).2 ⟨b, z, hz, rfl, rfl⟩, fun h' => hne (f.injective h')⟩

omit [Finite V] [Finite W] in
lemma IsBipartite.map [Nonempty W] (h : K.IsBipartite) : (K.map f).IsBipartite := by
  classical
  let g : V → W := fun v => if hv : ∃ a, f a = v then hv.choose else Classical.arbitrary W
  have hg : ∀ a, g (f a) = a := fun a => by
    have hv : ∃ a', f a' = f a := ⟨a, rfl⟩
    simp only [g, dite_eq_left hv]
    exact f.injective hv.choose_spec
  let φ : K.map f →g K :=
    { toFun := g
      map_rel' := by
        intro u v huv
        obtain ⟨a, b, hab, rfl, rfl⟩ := (map_adj f K u v).1 huv
        simpa [hg] using hab }
  exact Colorable.of_hom φ h

/-- If `K` has neither isolated vertices nor vertices of degree 1 and `K.map f` is planar, then
`|E(K)| + 6 ≤ 3 |W|`. -/
lemma edge_bound_map (h : NoLeaf K) (hK : ∀ a, ¬ K.IsIsolated a) {a b : W} (hab : K.Adj a b)
    (hP : IsPlanar (K.map f)) : K.edgeSet.ncard + 6 ≤ 3 * Nat.card W := by
  have := hP.edge_bound (h.map f) (u := f a) (v := f b) ((map_adj f K _ _).2 ⟨a, b, hab, rfl, rfl⟩)
  have hI := ncard_isolated_map K f hK
  rw [ncard_edgeSet_map] at this
  omega

lemma edge_bound_map_of_isBipartite [Nonempty W] (h : NoLeaf K) (hbip : K.IsBipartite)
    (hK : ∀ a, ¬ K.IsIsolated a) {a b : W} (hab : K.Adj a b) (hP : IsPlanar (K.map f)) :
    K.edgeSet.ncard + 4 ≤ 2 * Nat.card W := by
  have := hP.edge_bound_of_isBipartite (h.map f) (hbip.map f) (u := f a) (v := f b)
    ((map_adj f K _ _).2 ⟨a, b, hab, rfl, rfl⟩)
  have hI := ncard_isolated_map K f hK
  rw [ncard_edgeSet_map] at this
  omega

end Map

end Kuratowski

/-! ## `K₅` and `K₃,₃` -/

namespace Kuratowski

open SimpleGraph

/-- The complete graph `K₅`. -/
abbrev K5 : SimpleGraph (Fin 5) := ⊤

/-- The complete bipartite graph `K₃,₃`. -/
abbrev K33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

instance : DecidableRel K33.Adj := fun v w =>
  decidable_of_iff _ (Iff.of_eq (completeBipartiteGraph_adj (Fin 3) (Fin 3) v w).symm)

lemma K5_noLeaf : NoLeaf K5 := by
  unfold NoLeaf
  decide

lemma K33_noLeaf : NoLeaf K33 := by
  unfold NoLeaf
  decide +kernel

lemma K5_not_isolated (a : Fin 5) : ¬ K5.IsIsolated a := by
  unfold IsIsolated
  revert a
  decide

lemma K33_not_isolated (a : Fin 3 ⊕ Fin 3) : ¬ K33.IsIsolated a := by
  unfold IsIsolated
  revert a
  decide +kernel

lemma K5_ncard_edgeSet : K5.edgeSet.ncard = 10 := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two]
  rfl

lemma K33_ncard_edgeSet : K33.edgeSet.ncard = 9 := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  decide +kernel

/-- `K₅` placed in any finite vertex set is not planar. -/
theorem K5_map_not_isPlanar {V : Type*} [Finite V] (f : Fin 5 ↪ V) : ¬ IsPlanar (K5.map f) := by
  intro h
  have := edge_bound_map f K5_noLeaf K5_not_isolated (a := 0) (b := 1) (by decide) h
  rw [K5_ncard_edgeSet, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

/-- `K₃,₃` placed in any finite vertex set is not planar. -/
theorem K33_map_not_isPlanar {V : Type*} [Finite V] (f : Fin 3 ⊕ Fin 3 ↪ V) :
    ¬ IsPlanar (K33.map f) := by
  intro h
  have := edge_bound_map_of_isBipartite f K33_noLeaf (IsBipartite.completeBipartiteGraph _ _)
    K33_not_isolated (a := .inl 0) (b := .inr 0) (by decide +kernel) h
  rw [K33_ncard_edgeSet, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin] at this
  omega

/-- **`K₅` is not planar.** -/
theorem K5_not_isPlanar : ¬ IsPlanar K5 := by
  intro h
  have := h.edge_bound K5_noLeaf (u := 0) (v := 1) (by decide)
  have hI : {w | K5.IsIsolated w}.ncard = 0 := by
    rw [Set.ncard_eq_zero]
    exact Set.eq_empty_of_forall_notMem K5_not_isolated
  rw [K5_ncard_edgeSet, hI, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

/-- **`K₃,₃` is not planar.** -/
theorem K33_not_isPlanar : ¬ IsPlanar K33 := by
  intro h
  have := h.edge_bound_of_isBipartite K33_noLeaf (IsBipartite.completeBipartiteGraph _ _)
    (u := .inl 0) (v := .inr 0) (by decide +kernel)
  have hI : {w | K33.IsIsolated w}.ncard = 0 := by
    rw [Set.ncard_eq_zero]
    exact Set.eq_empty_of_forall_notMem K33_not_isolated
  rw [K33_ncard_edgeSet, hI, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin] at this
  omega

end Kuratowski
