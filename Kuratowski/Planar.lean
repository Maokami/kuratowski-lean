import Kuratowski.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# The definition is not vacuous: `K₄` is planar

If `IsPlanar` held for no graph, the non-planarity of `K₅` would be meaningless. We therefore
construct a rotation system of `K₄` with Euler characteristic 2.

A planar drawing of `K₄` has 4 faces (`4 - 6 + 4 = 2`). The rotation is as follows: at vertices
0 and 2 the other neighbors are visited in increasing cyclic order, at 1 and 3 in decreasing order.
-/

open Finset SimpleGraph

namespace Kuratowski

/-! ## A lemma for counting faces directly -/

/-- If a labelling is constant on cycles, separates distinct cycles, and uses every label, the
number of cycles equals the number of labels. -/
lemma card_quotient_sameCycle_eq {α β : Type*} [Finite α] (f : Equiv.Perm α) (lab : α → β)
    (hinv : ∀ x, lab (f x) = lab x) (hsame : ∀ x y, lab x = lab y → f.SameCycle x y)
    (hsurj : Function.Surjective lab) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid f)) = Nat.card β := by
  have hpow : ∀ (n : ℕ) x, lab ((f ^ n) x) = lab x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro x; rw [pow_succ', Equiv.Perm.mul_apply, hinv, ih]
  refine Nat.card_eq_of_bijective
    (Quotient.lift lab fun a b (hab : f.SameCycle a b) => ?_) ⟨?_, ?_⟩
  · obtain ⟨n, hn⟩ := hab.exists_nat_pow_eq
    rw [← hn, hpow]
  · rintro ⟨a⟩ ⟨b⟩ h
    exact Quotient.sound (hsame a b h)
  · intro c
    obtain ⟨a, rfl⟩ := hsurj c
    exact ⟨⟦a⟧, rfl⟩

lemma card_connectedComponent_eq_one {V : Type*} {G : SimpleGraph V} (h : G.Connected) :
    Nat.card G.ConnectedComponent = 1 := by
  have := h.preconnected.subsingleton_connectedComponent
  have : Nonempty G.ConnectedComponent := h.nonempty.map G.connectedComponentMk
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩

/-! ## The rotation system of `K₄` -/

/-- The complete graph `K₄`. -/
abbrev K4 : SimpleGraph (Fin 4) := ⊤

/-- The neighbor after `w` around vertex `v`. (`v` itself is sent to itself.) -/
def nxt : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 2, 3, 1], ![3, 1, 0, 2], ![1, 3, 2, 0], ![2, 0, 1, 3]]

/-- The inverse of `nxt v`. -/
def prv : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 3, 1, 2], ![2, 1, 3, 0], ![3, 0, 2, 1], ![1, 2, 0, 3]]

lemma nxt_adj : ∀ v w : Fin 4, v ≠ w → v ≠ nxt v w := by decide
lemma prv_adj : ∀ v w : Fin 4, v ≠ w → v ≠ prv v w := by decide
lemma prv_nxt : ∀ v w : Fin 4, prv v (nxt v w) = w := by decide
lemma nxt_prv : ∀ v w : Fin 4, nxt v (prv v w) = w := by decide

/-- The rotation on the darts of `K₄`. -/
def k4Rot : Equiv.Perm K4.Dart where
  toFun d := ⟨(d.fst, nxt d.fst d.snd), (top_adj _ _).2 (nxt_adj _ _ d.adj.ne)⟩
  invFun d := ⟨(d.fst, prv d.fst d.snd), (top_adj _ _).2 (prv_adj _ _ d.adj.ne)⟩
  left_inv _ := Dart.ext _ _ (Prod.ext rfl (prv_nxt _ _))
  right_inv _ := Dart.ext _ _ (Prod.ext rfl (nxt_prv _ _))

/-- The planar rotation system of `K₄`. -/
def k4RotationSystem : RotationSystem K4 where
  rot := k4Rot
  fst_rot _ := rfl
  sameCycle_rot := by
    have : ∀ d d' : K4.Dart, d.fst = d'.fst → ∃ i : Fin 3, (k4Rot ^ (i : ℕ)) d = d' := by
      decide +kernel
    intro d d' h
    obtain ⟨i, hi⟩ := this d d' h
    exact ⟨i, by simpa using hi⟩

/-- Face labels: the four faces of `K₄` are `{01, 13, 30}`, `{02, 21, 10}`, `{03, 32, 20}`,
`{12, 23, 31}`. -/
def k4FaceLabel (d : K4.Dart) : Fin 4 :=
  ![![0, 0, 1, 2], ![1, 0, 3, 0], ![2, 1, 0, 3], ![0, 3, 2, 0]] d.fst d.snd

lemma k4_card_face : Nat.card k4RotationSystem.Face = 4 := by
  rw [card_quotient_sameCycle_eq k4RotationSystem.facePerm k4FaceLabel, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  · decide +kernel
  · intro x y h
    have : ∀ x y : K4.Dart, k4FaceLabel x = k4FaceLabel y →
        ∃ i : Fin 3, (k4RotationSystem.facePerm ^ (i : ℕ)) x = y := by
      decide +kernel
    obtain ⟨i, hi⟩ := this x y h
    exact ⟨i, by simpa using hi⟩
  · have : ∀ c : Fin 4, ∃ d : K4.Dart, k4FaceLabel d = c := by decide +kernel
    exact this

/-- **`K₄` is planar.** Hence `IsPlanar` is not a vacuous definition. -/
theorem K4_isPlanar : IsPlanar K4 := by
  refine ⟨k4RotationSystem, ?_⟩
  have hV : Nat.card (Fin 4) = 4 := by simp
  have hE : K4.edgeSet.ncard = 6 := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two]
    rfl
  have hI : {v | K4.IsIsolated v}.ncard = 0 := by
    rw [Set.ncard_eq_zero]
    refine Set.eq_empty_of_forall_notMem fun v => ?_
    unfold IsIsolated
    revert v
    decide
  have hC : Nat.card K4.ConnectedComponent = 1 := card_connectedComponent_eq_one connected_top
  have hF : orbitCount k4RotationSystem.facePerm = 4 := k4_card_face
  unfold RotationSystem.eulerChar RotationSystem.numFaces
  rw [hF, hV, hE, hI, hC]
  norm_num

end Kuratowski
