import Kuratowski.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Deleting one edge

Deleting the edge of a dart `d = (u, v)` from a rotation system `R` removes `d` and `d.symm` from
the cyclic orders at their vertices. This gives a rotation system `R.del d` of `G - uv`.

The number of faces changes by exactly one.

* If `d` and `d.symm` lie on the same face, that face splits into two: `F' = F + 1`.
* Otherwise the two faces merge: `F' = F - 1`.

The proof works with face permutations. The face permutation of `R.del d` is
`φ * swap d d.symm` with `d` and `d.symm` cut out (`del_facePerm`). A transposition changes the
number of cycles by ±1 (`Kuratowski.Perm`), and cutting only creates fixed points. When `u` or `v`
becomes isolated, the isolated-vertex term of `numFaces` compensates exactly.

Moreover, if `d` and `d.symm` lie on different faces, following the face of `d` gives a path from
`v` to `u` that avoids `uv`, so `uv` is not a bridge (`reachable_del_of_not_sameCycle`).
-/

namespace Kuratowski

open Equiv Equiv.Perm SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Darts other than `d` and `d.symm` are darts of the graph with the edge of `d` deleted. -/
def delDartEquiv (d : G.Dart) :
    {x : G.Dart // x ≠ d ∧ x ≠ d.symm} ≃ (G.deleteEdges {d.edge}).Dart where
  toFun x := ⟨x.1.toProd, by
    rw [deleteEdges_adj]
    refine ⟨x.1.adj, fun h => ?_⟩
    have : x.1.edge = d.edge := h
    rcases (dart_edge_eq_iff _ _).1 this with h' | h'
    · exact x.2.1 h'
    · exact x.2.2 h'⟩
  invFun y := ⟨⟨y.toProd, (deleteEdges_adj.1 y.adj).1⟩, by
    have h := (deleteEdges_adj.1 y.adj).2
    constructor
    · rintro h'
      exact h (Set.mem_singleton_iff.2 (congrArg Dart.edge h'))
    · rintro h'
      exact h (Set.mem_singleton_iff.2 ((congrArg Dart.edge h').trans (Dart.edge_symm d)))⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq V] in
@[simp] lemma delDartEquiv_toProd (d : G.Dart) (x : {x : G.Dart // x ≠ d ∧ x ≠ d.symm}) :
    (delDartEquiv d x).toProd = x.1.toProd := rfl

omit [DecidableEq V] in
@[simp] lemma delDartEquiv_symm_toProd (d : G.Dart) (y : (G.deleteEdges {d.edge}).Dart) :
    ((delDartEquiv d).symm y).1.toProd = y.toProd := rfl

namespace RotationSystem

variable (R : RotationSystem G) (d : G.Dart)

/-- The rotation after deletion, on all darts: cut `d` and `d.symm` out of the cycle at each
vertex. -/
def rot₀ : Perm G.Dart := cut (cut R.rot d) d.symm

lemma rot₀_left : R.rot₀ d d = d := by
  unfold rot₀
  rw [cut_apply_of_ne _ (Dart.symm_ne d).symm, cut_apply_self]
  simp [(Dart.symm_ne d).symm]

lemma rot₀_right : R.rot₀ d d.symm = d.symm := cut_apply_self _ _

lemma rot₀_fst (x : G.Dart) : (R.rot₀ d x).fst = x.fst :=
  cut_preserves (cut R.rot d) d.symm (fun y : G.Dart => y.fst)
    (cut_preserves R.rot d (fun y : G.Dart => y.fst) R.fst_rot) x

omit [DecidableEq V] in
/-- A permutation with two fixed points preserves the set of the other points. -/
lemma pred_of_fix {f : Perm G.Dart} (h1 : f d = d) (h2 : f d.symm = d.symm) (x : G.Dart) :
    (f x ≠ d ∧ f x ≠ d.symm) ↔ (x ≠ d ∧ x ≠ d.symm) := by
  constructor
  · rintro ⟨hx1, hx2⟩
    exact ⟨fun h => hx1 (h ▸ h1), fun h => hx2 (h ▸ h2)⟩
  · rintro ⟨hx1, hx2⟩
    exact ⟨fun h => hx1 (f.injective (h.trans h1.symm)),
      fun h => hx2 (f.injective (h.trans h2.symm))⟩

/-- The rotation system of the graph with the edge of `d` deleted. -/
def del [Finite V] : RotationSystem (G.deleteEdges {d.edge}) where
  rot := (delDartEquiv d).permCongr
    ((R.rot₀ d).subtypePerm (pred_of_fix d (R.rot₀_left d) (R.rot₀_right d)))
  fst_rot y := R.rot₀_fst d _
  sameCycle_rot y y' h := by
    rw [← (delDartEquiv d).apply_symm_apply y, ← (delDartEquiv d).apply_symm_apply y',
      sameCycle_permCongr_iff, sameCycle_subtypePerm]
    set x := ((delDartEquiv d).symm y)
    set x' := ((delDartEquiv d).symm y')
    have hfst : x.1.fst = x'.1.fst := h
    unfold rot₀
    exact sameCycle_cut x.2.2 x'.2.2 (sameCycle_cut x.2.1 x'.2.1 (R.sameCycle_rot _ _ hfst))

/-- The face permutation after deletion, on all darts: `φ * swap d d.symm` with `d` and `d.symm`
cut out. -/
def face₀ : Perm G.Dart := cut (cut (R.facePerm * swap d d.symm) d) d.symm

lemma face₀_left : R.face₀ d d = d := by
  unfold face₀
  rw [cut_apply_of_ne _ (Dart.symm_ne d).symm, cut_apply_self]
  simp [(Dart.symm_ne d).symm]

lemma face₀_right : R.face₀ d d.symm = d.symm := cut_apply_self _ _

omit [DecidableEq V] in
lemma rot_symm_ne (x : G.Dart) (h : x.fst ≠ d.fst) : R.rot x ≠ d := fun h' =>
  h (by rw [← R.fst_rot x, h'])

lemma rot₀_symm (x : G.Dart) (hx1 : x ≠ d) (hx2 : x ≠ d.symm) :
    R.rot₀ d x.symm = R.face₀ d x := by
  have hs1 : x.symm ≠ d.symm := fun h => hx1 (Dart.symm_involutive.injective h)
  have hs2 : x.symm ≠ d := fun h => hx2 (by rw [← h, Dart.symm_symm])
  have hdd : d.symm ≠ d := Dart.symm_ne d
  have hψx : (R.facePerm * swap d d.symm) x = R.rot x.symm := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hx1 hx2, facePerm_apply]
  have hψd : (R.facePerm * swap d d.symm) d = R.rot d := by
    rw [Perm.mul_apply, swap_apply_left, facePerm_apply, Dart.symm_symm]
  have hψd' : (R.facePerm * swap d d.symm) d.symm = R.rot d.symm := by
    rw [Perm.mul_apply, swap_apply_right, facePerm_apply]
  have hrd : R.rot d.symm ≠ d := R.rot_symm_ne d d.symm (by simp)
  unfold rot₀ face₀
  rw [cut_apply_of_ne _ hs1, cut_apply_of_ne _ hx2, cut_apply_of_ne _ hs2,
    cut_apply_of_ne _ hx1, cut_apply_of_ne _ hdd, cut_apply_of_ne _ hdd, hψx, hψd, hψd']

lemma del_facePerm [Finite V] :
    (R.del d).facePerm = (delDartEquiv d).permCongr
      ((R.face₀ d).subtypePerm (pred_of_fix d (R.face₀_left d) (R.face₀_right d))) := by
  ext y : 1
  apply Dart.ext
  set x := (delDartEquiv d).symm y
  change (R.rot₀ d ((delDartEquiv d).symm y.symm).1).toProd = (R.face₀ d x.1).toProd
  have : ((delDartEquiv d).symm y.symm).1 = x.1.symm := Dart.ext _ _ rfl
  rw [this, R.rot₀_symm d x.1 x.2.1 x.2.2]

omit [DecidableEq V] in
/-- `rot` fixes `e` iff `e.snd` is the only neighbor of the start vertex of `e`. -/
lemma rot_eq_self_iff (e : G.Dart) : R.rot e = e ↔ ∀ z, G.Adj e.fst z → z = e.snd := by
  constructor
  · intro h z hz
    exact congrArg (fun x : G.Dart => x.snd) (R.eq_of_rot_eq_self h (d' := ⟨(e.fst, z), hz⟩) rfl)
  · intro h
    have hadj : G.Adj e.fst (R.rot e).snd := by
      have := (R.rot e).adj
      rwa [R.fst_rot] at this
    exact Dart.ext _ _ (Prod.ext (R.fst_rot e) (h _ hadj))

omit [DecidableEq V] in
lemma edge_eq_iff {p q : V} : s(p, q) = d.edge ↔ (p = d.fst ∧ q = d.snd) ∨ (p = d.snd ∧ q = d.fst) :=
  Sym2.eq_iff

/-- The only vertices that become isolated after deletion are endpoints of `d` of degree
1. -/
lemma isIsolated_del_iff (w : V) :
    (G.deleteEdges {d.edge}).IsIsolated w ↔
      G.IsIsolated w ∨ (w = d.fst ∧ R.rot d = d) ∨ (w = d.snd ∧ R.rot d.symm = d.symm) := by
  have hne : d.fst ≠ d.snd := d.fst_ne_snd
  have hadj : ∀ {p q}, (G.deleteEdges {d.edge}).Adj p q ↔ G.Adj p q ∧ s(p, q) ≠ d.edge := by
    intro p q
    simp [deleteEdges_adj]
  constructor
  · intro h
    by_cases hu : w = d.fst
    · refine Or.inr (Or.inl ⟨hu, (R.rot_eq_self_iff d).2 fun z hz => ?_⟩)
      by_contra hz'
      apply h z
      rw [hadj, hu]
      refine ⟨hz, fun he => ?_⟩
      rcases (edge_eq_iff d).1 he with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact hz' h2
      · exact hne h1
    by_cases hv : w = d.snd
    · refine Or.inr (Or.inr ⟨hv, (R.rot_eq_self_iff d.symm).2 fun z hz => ?_⟩)
      by_contra hz'
      apply h z
      rw [hadj, hv]
      refine ⟨hz, fun he => ?_⟩
      rcases (edge_eq_iff d).1 he with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hne h1.symm
      · exact hz' h2
    · refine Or.inl fun z hz => h z (hadj.2 ⟨hz, fun he => ?_⟩)
      rcases (edge_eq_iff d).1 he with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hu h1
      · exact hv h1
  · rintro (h | ⟨rfl, h⟩ | ⟨rfl, h⟩) z hz
    · exact h z (hadj.1 hz).1
    · have := (R.rot_eq_self_iff d).1 h z (hadj.1 hz).1
      exact (hadj.1 hz).2 (by rw [this]; rfl)
    · have := (R.rot_eq_self_iff d.symm).1 h z (hadj.1 hz).1
      exact (hadj.1 hz).2 (by rw [this]; exact Dart.edge_symm d)

lemma ncard_isolated_del [Finite V] :
    {w | (G.deleteEdges {d.edge}).IsIsolated w}.ncard =
      {w | G.IsIsolated w}.ncard + (if R.rot d = d then 1 else 0) +
        (if R.rot d.symm = d.symm then 1 else 0) := by
  have hS : {w | (G.deleteEdges {d.edge}).IsIsolated w} =
      ({w | G.IsIsolated w} ∪ {w | w = d.fst ∧ R.rot d = d}) ∪
        {w | w = d.snd ∧ R.rot d.symm = d.symm} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    rw [R.isIsolated_del_iff]
    tauto
  have hA : {w | w = d.fst ∧ R.rot d = d}.ncard = if R.rot d = d then 1 else 0 := by
    split_ifs with h <;> simp [h]
  have hB : {w | w = d.snd ∧ R.rot d.symm = d.symm}.ncard =
      if R.rot d.symm = d.symm then 1 else 0 := by
    split_ifs with h <;> simp [h]
  rw [hS, Set.ncard_union_eq, Set.ncard_union_eq, hA, hB]
  · exact Set.disjoint_left.2 fun w h1 h2 => h1 d.snd (by rw [h2.1]; exact d.adj)
  · refine Set.disjoint_left.2 fun w h1 h2 => ?_
    rcases h1 with h1 | h1
    · exact h1 d.fst (by rw [h2.1]; exact d.adj.symm)
    · exact d.fst_ne_snd (h1.1.symm.trans h2.1)

/-- **Face count formula**: after deleting the edge of `d`, the number of faces is the number of
cycles of `φ * swap d d.symm` plus the original number of isolated vertices. -/
theorem numFaces_del [Finite V] :
    (R.del d).numFaces = orbitCount (R.facePerm * swap d d.symm) + {w | G.IsIsolated w}.ncard := by
  set ψ := R.facePerm * swap d d.symm with hψ
  have hdd : d.symm ≠ d := Dart.symm_ne d
  have hψd : ψ d = R.rot d := by
    rw [hψ, Perm.mul_apply, swap_apply_left, facePerm_apply, Dart.symm_symm]
  have hψd' : ψ d.symm = R.rot d.symm := by
    rw [hψ, Perm.mul_apply, swap_apply_right, facePerm_apply]
  have hrd : R.rot d.symm ≠ d := R.rot_symm_ne d d.symm (by simp)
  have hcut : cut ψ d d.symm = R.rot d.symm := by
    rw [cut_apply_of_ne _ hdd, hψd']
    simp [hrd]
  have hp := pred_of_fix d (R.face₀_left d) (R.face₀_right d)
  have h1 : orbitCount (R.del d).facePerm =
      orbitCount ((R.face₀ d).subtypePerm (p := fun x => x ≠ d ∧ x ≠ d.symm) hp) := by
    rw [del_facePerm, orbitCount_permCongr]
  have h2 := orbitCount_eq_subtypePerm_add (R.face₀ d) (fun x => x ≠ d ∧ x ≠ d.symm) hp (by
      intro x hx
      by_cases h : x = d
      · rw [h, R.face₀_left]
      · have : x = d.symm := by
          by_contra h'
          exact hx ⟨h, h'⟩
        rw [this, R.face₀_right])
  have h3 : Nat.card {x : G.Dart // ¬(x ≠ d ∧ x ≠ d.symm)} = 2 := by
    have : {x : G.Dart | ¬(x ≠ d ∧ x ≠ d.symm)} = {d, d.symm} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    change Nat.card ↥{x : G.Dart | ¬(x ≠ d ∧ x ≠ d.symm)} = 2
    rw [Nat.card_coe_set_eq, this, Set.ncard_pair hdd.symm]
  have h4 : orbitCount (R.face₀ d) = orbitCount (cut ψ d) +
      if cut ψ d d.symm = d.symm then 0 else 1 := orbitCount_cut _ _
  have h5 : orbitCount (cut ψ d) = orbitCount ψ + if ψ d = d then 0 else 1 := orbitCount_cut _ _
  have h6 := R.ncard_isolated_del d
  rw [hcut] at h4
  rw [hψd] at h5
  unfold numFaces
  rw [h1, h6]
  split_ifs at h4 h5 ⊢ <;> omega

theorem numFaces_del_of_sameCycle [Finite V] (h : SameCycle R.facePerm d d.symm) :
    (R.del d).numFaces = R.numFaces + 1 := by
  rw [numFaces_del, orbitCount_mul_swap_of_sameCycle (Dart.symm_ne d).symm h, numFaces]
  omega

theorem numFaces_del_of_not_sameCycle [Finite V] (h : ¬ SameCycle R.facePerm d d.symm) :
    (R.del d).numFaces + 1 = R.numFaces := by
  rw [numFaces_del, numFaces, ← orbitCount_mul_swap_of_not_sameCycle h]
  omega

/-- If `d` and `d.symm` lie on different faces, following the face of `d` gives a path from
`d.snd` to `d.fst` in the graph after deletion. Hence the edge of `d` is not a bridge. -/
theorem reachable_del_of_not_sameCycle [Finite V] (h : ¬ SameCycle R.facePerm d d.symm) :
    (G.deleteEdges {d.edge}).Reachable d.fst d.snd := by
  have key : ∀ k : ℕ, (G.deleteEdges {d.edge}).Reachable d.snd ((R.facePerm ^ (k + 1)) d).fst := by
    intro k
    induction k with
    | zero => rw [zero_add, pow_one, facePerm_fst]
    | succ k ih =>
      rw [pow_succ', Perm.mul_apply, facePerm_fst]
      by_cases hz : (R.facePerm ^ (k + 1)) d = d
      · rw [hz]
      · have hz' : (R.facePerm ^ (k + 1)) d ≠ d.symm := fun hz' =>
          h (by rw [← hz']; exact sameCycle_pow_right.2 (SameCycle.refl _ _))
        exact ih.trans (delDartEquiv d ⟨_, hz, hz'⟩).adj.reachable
  obtain ⟨m, hm⟩ := (sameCycle_apply_left.2 (SameCycle.refl R.facePerm d)).exists_nat_pow_eq
  have hm' : (R.facePerm ^ (m + 1)) d = d := by rw [pow_succ, Perm.mul_apply, hm]
  have := key m
  rw [hm'] at this
  exact this.symm

end RotationSystem

end Kuratowski
