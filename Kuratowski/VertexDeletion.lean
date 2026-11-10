import Kuratowski.Connected
import Kuratowski.Euler

/-!
# Deleting a vertex (blueprint `def:delVertex`)

From a rotation system `R` we build a rotation system `R.delVertex v` of
`deleteVertices G {v}`, the graph with all edges at `v` deleted. Since the graph is simple, the
only dart at a vertex `u ≠ v` that gets deleted is `(u, v)`. Hence the new rotation is `ρ (ρ x)`,
one step further, if `ρ x` goes to `v`, and `ρ x` otherwise (`delVertex_rot_toProd`). `ρ (ρ x)`
does not go to `v` again (`snd_rot_rot_ne`).

The construction iterates single-edge deletion (`RotationSystem.del`, theorem `thm:del`) over the
neighbors of `v`. Each step preserves the skipping formula above (`exists_rot_deleteEdges_star`)
and genus 0 (`eulerChar_del_eq_of_eq`). So after deleting a vertex of a planar graph, this
rotation system still witnesses planarity (`IsPlanar.deleteVertex`).
-/

namespace Kuratowski

open Equiv Equiv.Perm SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The edges from `v` to the vertices of `W`. -/
def star (v : V) (W : Set V) : Set (Sym2 V) := {e | ∃ w ∈ W, e = s(v, w)}

namespace RotationSystem

variable (R : RotationSystem G)

open Classical in
/-- The skipping formula: if `ρ x` is a dart from a vertex of `W` to `v`, take one more step. -/
noncomputable def skip (v : V) (W : Set V) (x : G.Dart) : G.Dart :=
  if (R.rot x).snd = v ∧ (R.rot x).fst ∈ W then R.rot (R.rot x) else R.rot x

/-- If `x` does not go to `v` but `ρ x` does, then `ρ (ρ x)` does not go to `v`. Otherwise
`ρ (ρ x) = ρ x`, since only one dart from a given vertex goes to `v`, and injectivity gives
`ρ x = x`. -/
theorem snd_rot_rot_ne {v : V} {x : G.Dart} (hx : x.snd ≠ v) (h : (R.rot x).snd = v) :
    (R.rot (R.rot x)).snd ≠ v := by
  intro h'
  have he : R.rot (R.rot x) = R.rot x := by
    apply Dart.ext
    rw [Prod.ext_iff]
    exact ⟨by rw [R.fst_rot, R.fst_rot], h'.trans h.symm⟩
  have := R.rot.injective he
  exact hx (this ▸ h)

/-- Deleting one edge on the same vertex type preserves genus 0. -/
theorem eulerChar_del_eq_of_eq [Finite V] [DecidableEq V] {H : SimpleGraph V}
    (R : RotationSystem H) (d : H.Dart)
    (hR : R.eulerChar = 2 * Nat.card H.ConnectedComponent) :
    (R.del d).eulerChar = 2 * Nat.card (H.deleteEdges {d.edge}).ConnectedComponent := by
  refine le_antisymm (R.del d).eulerChar_le ?_
  by_cases h : SameCycle R.facePerm d d.symm
  · have hχ := R.eulerChar_del_of_sameCycle d h
    have hc : Nat.card (H.deleteEdges {d.edge}).ConnectedComponent ≤
        Nat.card H.ConnectedComponent + 1 := card_connectedComponent_deleteEdges_le H _ _
    omega
  · have hχ := R.eulerChar_del_of_not_sameCycle d h
    have hc : Nat.card (H.deleteEdges {d.edge}).ConnectedComponent =
        Nat.card H.ConnectedComponent :=
      card_connectedComponent_deleteEdges_eq H (R.reachable_del_of_not_sameCycle d h)
    rw [hc]
    omega

/-- The rotation of `R.del d`: for a dart `x ≠ d.symm` not starting at the start vertex of `d`,
it is `ρ d.symm` if `ρ x = d.symm`, and `ρ x` otherwise. -/
theorem rot₀_of_fst_ne [DecidableEq V] {H : SimpleGraph V} (R : RotationSystem H) (d x : H.Dart)
    (hx : x.fst ≠ d.fst) (hx' : x ≠ d.symm) (hd : d.snd ≠ d.fst) :
    R.rot₀ d x = if R.rot x = d.symm then R.rot d.symm else R.rot x := by
  have hxd : x ≠ d := fun e ↦ hx (by rw [e])
  have hgx : R.rot x ≠ d := fun e ↦ hx (by rw [← R.fst_rot x, e])
  have hgd : R.rot d.symm ≠ d := by
    intro e
    have h := R.fst_rot d.symm
    rw [e] at h
    exact hd h.symm
  have hdd : d.symm ≠ d := Dart.symm_ne d
  unfold rot₀
  rw [cut_apply_of_ne _ hx', cut_apply_of_ne _ hxd, cut_apply_of_ne _ hdd]
  simp only [hgx, hgd, ↓reduceIte]

/-- The rotation system obtained by deleting the edges to the neighbors `W` one by one. The
skipping formula holds at darts of vertices other than `v`, and genus 0 is preserved. The graph is
generalized by an equation so that it can be transported without casts. -/
theorem exists_rot_deleteEdges_star [Finite V] [DecidableEq V] (R : RotationSystem G) (v : V)
    (W : Finset V) (hW : (W : Set V) ⊆ G.neighborSet v) :
    ∀ H : SimpleGraph V, G.deleteEdges (star v W) = H → ∃ R' : RotationSystem H,
      (∀ (x : H.Dart) (y : G.Dart), x.toProd = y.toProd → y.fst ≠ v →
        (R'.rot x).toProd = (R.skip v W y).toProd) ∧
      (R.eulerChar = 2 * Nat.card G.ConnectedComponent →
        R'.eulerChar = 2 * Nat.card H.ConnectedComponent) := by
  induction W using Finset.induction_on with
  | empty =>
    intro H hH
    have h0 : star v ((∅ : Finset V) : Set V) = ∅ := by
      ext e
      simp [star]
    rw [h0, deleteEdges_empty] at hH
    subst hH
    refine ⟨R, fun x y hxy _ ↦ ?_, id⟩
    have : x = y := Dart.ext _ _ hxy
    subst this
    simp [skip]
  | @insert w W hwW ih =>
    intro H hH
    have hW' : (W : Set V) ⊆ G.neighborSet v := fun a ha ↦ hW (by simp [ha])
    have hvw : G.Adj v w := hW (by simp)
    obtain ⟨R', hR'rot, hR'χ⟩ := ih hW' _ rfl
    have hd : (G.deleteEdges (star v W)).Adj v w := by
      rw [deleteEdges_adj]
      refine ⟨hvw, ?_⟩
      rintro ⟨w', hw', he⟩
      rcases Sym2.eq_iff.1 he with ⟨-, rfl⟩ | ⟨h1, h2⟩
      · exact hwW hw'
      · exact hvw.ne h2.symm
    let d : (G.deleteEdges (star v W)).Dart := ⟨(v, w), hd⟩
    have hgraph : (G.deleteEdges (star v W)).deleteEdges {d.edge} = H := by
      rw [← hH, deleteEdges_deleteEdges]
      congr 1
      ext e
      simp only [star, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff, Finset.coe_insert,
        Set.mem_insert_iff, Finset.mem_coe, exists_eq_or_imp, d, Dart.edge]
      exact or_comm
    subst hgraph
    refine ⟨R'.del d, ?_, fun h ↦ eulerChar_del_eq_of_eq R' d (hR'χ h)⟩
    intro x y hxy hyv
    set x₁ := ((delDartEquiv d).symm x).1 with hx₁
    have hx₁p : x₁.toProd = y.toProd := hxy
    have hx₁ne := ((delDartEquiv d).symm x).2
    change (R'.rot₀ d x₁).toProd = _
    have hfst : x₁.fst ≠ d.fst := by
      change x₁.toProd.1 ≠ v
      rw [hx₁p]
      exact hyv
    rw [rot₀_of_fst_ne R' d x₁ hfst hx₁ne.2 hvw.ne.symm]
    have IH1 := hR'rot x₁ y hx₁p hyv
    let ŷ : G.Dart := ⟨(w, v), hvw.symm⟩
    have IH2 := hR'rot d.symm ŷ rfl hvw.ne.symm
    have hskipŷ : R.skip v W ŷ = R.rot ŷ := by
      unfold skip
      refine ite_eq_right_of_eq_false _ _ (eq_false ?_)
      rintro ⟨-, h⟩
      rw [R.fst_rot] at h
      exact hwW h
    split_ifs with hc
    · have h1 : (R.skip v W y).toProd = (w, v) := by
        rw [← IH1, hc]
        rfl
      have hρy : R.rot y = ŷ := by
        unfold skip at h1
        split_ifs at h1 with hcW
        · exfalso
          have h3 : (R.rot (R.rot y)).fst = w := congrArg Prod.fst h1
          rw [R.fst_rot, R.fst_rot] at h3
          have h2 := hcW.2
          rw [R.fst_rot, h3] at h2
          exact hwW h2
        · exact Dart.ext _ _ h1
      rw [IH2, hskipŷ]
      unfold skip
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [hρy], by rw [hρy]; simp [ŷ]⟩), hρy]
    · rw [IH1]
      unfold skip
      by_cases h1 : (R.rot y).snd = v ∧ (R.rot y).fst ∈ (W : Set V)
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h1),
          ite_eq_left_of_eq_true _ _ (eq_true ⟨h1.1, by simp [h1.2]⟩)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
        by_cases h2 : (R.rot y).snd = v ∧ (R.rot y).fst ∈ ((insert w W : Finset V) : Set V)
        · exfalso
          have hw : (R.rot y).fst = w := by
            have := h2.2
            simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at this
            rcases this with h | h
            · exact h
            · exact absurd ⟨h2.1, h⟩ h1
          apply hc
          apply Dart.ext
          rw [IH1]
          unfold skip
          rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
          exact Prod.ext hw h2.1
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]

/-- Two rotation systems with the same rotation are equal. -/
theorem ext_rot {H : SimpleGraph V} {R₁ R₂ : RotationSystem H} (h : R₁.rot = R₂.rot) : R₁ = R₂ := by
  cases R₁
  cases R₂
  cases h
  rfl

end RotationSystem

/-- Deleting the edges from `v` to all its neighbors gives the graph with `v` deleted. -/
theorem deleteEdges_star_neighborSet (v : V) :
    G.deleteEdges (star v (G.neighborSet v)) = deleteVertices G {v} := by
  ext a b
  rw [deleteEdges_adj, deleteVertices_adj]
  constructor
  · rintro ⟨hab, hn⟩
    refine ⟨hab, fun ha ↦ hn ?_, fun hb ↦ hn ?_⟩
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact ⟨b, hab, rfl⟩
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact ⟨a, hab.symm, Sym2.eq_swap⟩
  · rintro ⟨hab, ha, hb⟩
    refine ⟨hab, ?_⟩
    rintro ⟨w, -, he⟩
    rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact ha (Set.mem_singleton_iff.2 h1)
    · exact hb (Set.mem_singleton_iff.2 h2)

namespace RotationSystem

variable [Finite V] [DecidableEq V] (R : RotationSystem G) (v : V)

/-- There is a rotation system with `v` deleted: at good darts it is `ρ (ρ x)` if `ρ x` goes to
`v`, and `ρ x` otherwise; genus 0 is preserved. -/
theorem exists_delVertex : ∃ R' : RotationSystem (deleteVertices G {v}),
    (∀ (x : (deleteVertices G {v}).Dart) (y : G.Dart), x.toProd = y.toProd →
      (R'.rot x).toProd = (if (R.rot y).snd = v then R.rot (R.rot y) else R.rot y).toProd) ∧
    (R.eulerChar = 2 * Nat.card G.ConnectedComponent →
      R'.eulerChar = 2 * Nat.card (deleteVertices G {v}).ConnectedComponent) := by
  classical
  let N : Finset V := (G.neighborSet v).toFinite.toFinset
  have hN : (N : Set V) = G.neighborSet v := Set.Finite.coe_toFinset _
  have hgraph : G.deleteEdges (star v N) = deleteVertices G {v} := by
    rw [hN, deleteEdges_star_neighborSet]
  obtain ⟨R', hrot, hχ⟩ := exists_rot_deleteEdges_star R v N hN.le _ hgraph
  refine ⟨R', fun x y hxy ↦ ?_, hχ⟩
  have hyv : y.fst ≠ v := by
    intro h
    apply x.adj.2.1
    rw [Set.mem_singleton_iff]
    exact (congrArg Prod.fst hxy).trans h
  rw [hrot x y hxy hyv]
  unfold skip
  by_cases h : (R.rot y).snd = v
  · have hmem : (R.rot y).fst ∈ (N : Set V) := by
      rw [hN]
      have := (R.rot y).adj
      rw [h] at this
      exact this.symm
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h, hmem⟩)]
    simp only [h, ↓reduceIte]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun hc ↦ h hc.1)]
    simp only [h, ↓reduceIte]

/-- The rotation system with the vertex `v` deleted (blueprint `def:delVertex`). -/
noncomputable def delVertex : RotationSystem (deleteVertices G {v}) :=
  (R.exists_delVertex v).choose

/-- Correspondence: after deletion, the rotation skips the darts going to `v`. -/
theorem delVertex_rot_toProd (x : (deleteVertices G {v}).Dart) (y : G.Dart)
    (hxy : x.toProd = y.toProd) :
    ((R.delVertex v).rot x).toProd =
      (if (R.rot y).snd = v then R.rot (R.rot y) else R.rot y).toProd :=
  (R.exists_delVertex v).choose_spec.1 x y hxy

theorem delVertex_rot_of_snd_ne (x : (deleteVertices G {v}).Dart) (y : G.Dart)
    (hxy : x.toProd = y.toProd) (h : (R.rot y).snd ≠ v) :
    ((R.delVertex v).rot x).toProd = (R.rot y).toProd := by
  rw [R.delVertex_rot_toProd v x y hxy]
  simp only [h, ↓reduceIte]

/-- If `ρ x` goes to `v`, skip one step. Then `ρ (ρ x)` does not go to `v`
(`snd_rot_rot_ne`). -/
theorem delVertex_rot_of_snd_eq (x : (deleteVertices G {v}).Dart) (y : G.Dart)
    (hxy : x.toProd = y.toProd) (h : (R.rot y).snd = v) :
    ((R.delVertex v).rot x).toProd = (R.rot (R.rot y)).toProd := by
  rw [R.delVertex_rot_toProd v x y hxy]
  simp only [h, ↓reduceIte]

/-- The face permutation after deletion: skip the dart from `x̄` going to `v`. -/
theorem delVertex_facePerm_toProd (x : (deleteVertices G {v}).Dart) (y : G.Dart)
    (hxy : x.toProd = y.toProd) :
    ((R.delVertex v).facePerm x).toProd =
      (if (R.rot y.symm).snd = v then R.rot (R.rot y.symm) else R.rot y.symm).toProd := by
  rw [facePerm_apply]
  exact R.delVertex_rot_toProd v x.symm y.symm (by
    change x.toProd.swap = y.toProd.swap
    rw [hxy])

/-- `delVertex` is the only rotation system satisfying this correspondence. -/
theorem eq_delVertex (R'' : RotationSystem (deleteVertices G {v}))
    (h : ∀ (x : (deleteVertices G {v}).Dart) (y : G.Dart), x.toProd = y.toProd →
      (R''.rot x).toProd = (if (R.rot y).snd = v then R.rot (R.rot y) else R.rot y).toProd) :
    R'' = R.delVertex v := by
  apply ext_rot
  ext x : 1
  apply Dart.ext
  let y : G.Dart := ⟨x.toProd, x.adj.1⟩
  rw [h x y rfl, R.delVertex_rot_toProd v x y rfl]

/-- Genus 0 is preserved. -/
theorem eulerChar_delVertex (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) :
    (R.delVertex v).eulerChar = 2 * Nat.card (deleteVertices G {v}).ConnectedComponent :=
  (R.exists_delVertex v).choose_spec.2 hR

end RotationSystem

/-- Deleting a vertex of a planar graph gives a planar graph, witnessed by the rotation system
`R.delVertex` built by skipping. -/
theorem IsPlanar.deleteVertex [Finite V] [DecidableEq V] (hG : IsPlanar G) (v : V) :
    IsPlanar (deleteVertices G {v}) := by
  obtain ⟨R, hR⟩ := hG
  exact ⟨R.delVertex v, R.eulerChar_delVertex v hR⟩

end Kuratowski
