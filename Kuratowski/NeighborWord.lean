import Kuratowski.VertexSplit
import Kuratowski.CyclicWord
import Kuratowski.DelVertexFace
import Mathlib.Tactic.Abel

/-!
# Cyclic word classification and the interval condition for actual rotations

If a `Clustered` word covers every position by `X` or `Y`, we can choose a starting point and a cut
position. Applied to the word read from the reversed neighbor sequence of a contracted rotation,
this gives the `IntervalWord` needed for vertex splitting. We also prove that an increasing
sequence of natural-number positions preserves the open cyclic order; this transfers an
alternating pattern to an actual cycle through the position sequence of J2. Instead of a regular
expression library, we work with explicit interval conditions on finite cyclic positions.
-/

namespace Kuratowski.CyclicWord

/-- A closed arc with distinct endpoints is its two endpoints together with the open arc. -/
lemma btw_iff_eq_or_sbtw {n : ℕ} [NeZero n] {a t b : ZMod n} (hab : a ≠ b) :
    btw a t b ↔ t = a ∨ t = b ∨ sbtw a t b := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    change ((a : Fin (n + 1)).val ≤ (t : Fin (n + 1)).val ∧
      (t : Fin (n + 1)).val ≤ (b : Fin (n + 1)).val ∨
      (t : Fin (n + 1)).val ≤ (b : Fin (n + 1)).val ∧
      (b : Fin (n + 1)).val ≤ (a : Fin (n + 1)).val ∨
      (b : Fin (n + 1)).val ≤ (a : Fin (n + 1)).val ∧
      (a : Fin (n + 1)).val ≤ (t : Fin (n + 1)).val) ↔
      t = a ∨ t = b ∨ ((a : Fin (n + 1)).val < (t : Fin (n + 1)).val ∧
      (t : Fin (n + 1)).val < (b : Fin (n + 1)).val ∨
      (t : Fin (n + 1)).val < (b : Fin (n + 1)).val ∧
      (b : Fin (n + 1)).val < (a : Fin (n + 1)).val ∨
      (b : Fin (n + 1)).val < (a : Fin (n + 1)).val ∧
      (a : Fin (n + 1)).val < (t : Fin (n + 1)).val)
    have hta : t = a ↔ t.val = a.val := (ZMod.val_injective (n + 1)).eq_iff.symm
    have htb : t = b ↔ t.val = b.val := (ZMod.val_injective (n + 1)).eq_iff.symm
    rw [hta, htb]
    have habval : a.val ≠ b.val := fun h ↦ hab (ZMod.val_injective _ h)
    omega

/-- Modular distance criterion for a closed arc. The endpoints must be distinct. -/
lemma btw_iff_val_le {n : ℕ} [NeZero n] {a t b : ZMod n} (hab : a ≠ b) :
    btw a t b ↔ (t - a).val ≤ (b - a).val := by
  rw [btw_iff_eq_or_sbtw hab, sbtw_iff_val]
  have ht : (t - a).val = 0 ↔ t = a := by
    rw [ZMod.val_eq_zero, sub_eq_zero]
  have htb : (t - a).val = (b - a).val ↔ t = b := by
    rw [(ZMod.val_injective n).eq_iff, sub_left_inj]
  have hpos : 0 < (b - a).val := Nat.pos_of_ne_zero (fun h ↦
    hab (sub_eq_zero.mp ((ZMod.val_eq_zero (b - a)).mp h)).symm)
  rw [← ht, ← htb]
  omega

/-- If `X` and `Y` cover every position, a `Clustered` word is described by a starting point and
one cut position. -/
theorem clustered_interval {n : ℕ} [NeZero n] (X Y : Finset (ZMod n))
    (hcover : ∀ i, i ∈ X ∨ i ∈ Y) (h : Clustered X Y) :
    ∃ b : ZMod n, ∃ k ≤ n,
      (∀ j < k, b + (j : ZMod n) ∈ X) ∧
      (∀ j, k ≤ j → j < n → b + (j : ZMod n) ∉ X) ∧
      ∀ j, 0 < j → j + 1 < k → b + (j : ZMod n) ∉ Y := by
  obtain ⟨a, b, hab, hY⟩ := h
  let l := (a - b).val
  have hl : l < n := ZMod.val_lt _
  have hval : ∀ j < n, (b + (j : ZMod n) - b).val = j := by
    intro j hj
    rw [show b + (j : ZMod n) - b = (j : ZMod n) by abel]
    simpa using ZMod.val_natCast_of_lt hj
  have at_end : b + (l : ZMod n) = a := by
    simp only [l, ZMod.natCast_zmod_val]
    abel
  have hinner : ∀ j, 0 < j → j < l → ¬ btw a (b + (j : ZMod n)) b := by
    intro j hj hjl
    apply not_btw_of_sbtw
    rw [sbtw_iff_val, hval j (lt_trans hjl hl)]
    exact ⟨hj, hjl⟩
  refine ⟨b, l + 1, by omega, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hj0 : j = 0
    · simpa [hj0] using hab.2.1
    by_cases hjl : j = l
    · rw [hjl, at_end]
      exact hab.1
    exact (hcover _).resolve_right (fun hy ↦ hinner j (by omega) (by omega) (hY _ hy))
  · intro j hkj hjn hjX
    apply hab.2.2.2 _ hjX
    rw [sbtw_iff_not_btw, btw_iff_val_le hab.2.2.1.symm, hval j hjn]
    exact Nat.not_le.mpr (by omega)
  · intro j hj hjk hjY
    exact hinner j hj (by omega) (hY _ hjY)

end Kuratowski.CyclicWord
namespace Kuratowski.CyclicWord

/-- An increasing position sequence preserves the open cyclic order. -/
theorem sbtw_cast_positions {N m : ℕ} [NeZero N] [NeZero m]
    (p : ℕ → ℕ) (hp : ∀ j, j < N → p j < m)
    (hinc : ∀ j, j + 1 < N → p j < p (j + 1)) {a t b : ZMod N}
    (h : sbtw a t b) :
    sbtw (p a.val : ZMod m) (p t.val : ZMod m) (p b.val : ZMod m) := by
  have hmono : ∀ i j, i < j → j < N → p i < p j := by
    intro i j
    induction j with
    | zero => intro hij; omega
    | succ j ih =>
      intro hij hj
      by_cases heq : i = j
      · subst i
        exact hinc j hj
      · exact (ih (by omega) (by omega)).trans (hinc j hj)
  have hv : ∀ j, j < N → (p j : ZMod m).val = p j := by
    intro j hj
    exact ZMod.val_natCast_of_lt (hp j hj)
  have src : (a.val < t.val ∧ t.val < b.val) ∨
      (t.val < b.val ∧ b.val < a.val) ∨ (b.val < a.val ∧ a.val < t.val) := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => exact h
  have hat : a.val < N := ZMod.val_lt a
  have htt : t.val < N := ZMod.val_lt t
  have hbt : b.val < N := ZMod.val_lt b
  have target : ((p a.val : ZMod m).val < (p t.val : ZMod m).val ∧
      (p t.val : ZMod m).val < (p b.val : ZMod m).val) ∨
      ((p t.val : ZMod m).val < (p b.val : ZMod m).val ∧
      (p b.val : ZMod m).val < (p a.val : ZMod m).val) ∨
      ((p b.val : ZMod m).val < (p a.val : ZMod m).val ∧
      (p a.val : ZMod m).val < (p t.val : ZMod m).val) := by
    rw [hv a.val hat, hv t.val htt, hv b.val hbt]
    rcases src with h | h | h
    · exact Or.inl ⟨hmono _ _ h.1 htt, hmono _ _ h.2 hbt⟩
    · exact Or.inr (Or.inl ⟨hmono _ _ h.1 hbt, hmono _ _ h.2 hat⟩)
    · exact Or.inr (Or.inr ⟨hmono _ _ h.1 hat, hmono _ _ h.2 htt⟩)
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact target

end Kuratowski.CyclicWord

namespace Kuratowski
open SimpleGraph Equiv Equiv.Perm Function
variable {V : Type*} {G : SimpleGraph V} {x y : V}

namespace RotationSystem

/-- The word recording adjacency to the two original vertices along the reversed neighbor
sequence of a contracted rotation. -/
noncomputable def neighborWord (R : RotationSystem (contractEdge G x y))
    (d₀ : (contractEdge G x y).Dart) :
    ZMod ((contractEdge G x y).neighborSet x).ncard → CyclicWord.Letter := by
  classical
  exact fun i ↦ if G.Adj x ((R.rot⁻¹ ^ i.val) d₀).snd then
    if G.Adj y ((R.rot⁻¹ ^ i.val) d₀).snd then .both else .x
    else if G.Adj y ((R.rot⁻¹ ^ i.val) d₀).snd then .y else .blank

variable [NeZero ((contractEdge G x y).neighborSet x).ncard]

lemma mem_xPositions_neighborWord (R : RotationSystem (contractEdge G x y))
    (d₀ : (contractEdge G x y).Dart) {i : ZMod ((contractEdge G x y).neighborSet x).ncard} :
    i ∈ CyclicWord.xPositions (R.neighborWord d₀) ↔ G.Adj x ((R.rot⁻¹ ^ i.val) d₀).snd := by
  classical
  by_cases hx : G.Adj x ((R.rot⁻¹ ^ i.val) d₀).snd <;>
    by_cases hy : G.Adj y ((R.rot⁻¹ ^ i.val) d₀).snd <;>
      simp_all [neighborWord, CyclicWord.xPositions]

lemma mem_yPositions_neighborWord (R : RotationSystem (contractEdge G x y))
    (d₀ : (contractEdge G x y).Dart) {i : ZMod ((contractEdge G x y).neighborSet x).ncard} :
    i ∈ CyclicWord.yPositions (R.neighborWord d₀) ↔ G.Adj y ((R.rot⁻¹ ^ i.val) d₀).snd := by
  classical
  by_cases hx : G.Adj x ((R.rot⁻¹ ^ i.val) d₀).snd <;>
    by_cases hy : G.Adj y ((R.rot⁻¹ ^ i.val) d₀).snd <;>
      simp_all [neighborWord, CyclicWord.yPositions]

lemma neighborWord_cover (R : RotationSystem (contractEdge G x y))
    (d₀ : (contractEdge G x y).Dart) (hd₀ : d₀.fst = x) :
    ∀ i, i ∈ CyclicWord.xPositions (R.neighborWord d₀) ∨
      i ∈ CyclicWord.yPositions (R.neighborWord d₀) := by
  intro i
  have ha := ((R.rot⁻¹ ^ i.val) d₀).adj
  rw [R.fst_rot_inv_pow, hd₀] at ha
  rcases adj_x_or_adj_y_of_contractEdge_adj ha with hx | hy
  · exact Or.inl (R.mem_xPositions_neighborWord d₀ |>.2 hx)
  · exact Or.inr (R.mem_yPositions_neighborWord d₀ |>.2 hy)

/-- The first case of the cyclic word classification gives the interval condition for the
actual rotation. -/
theorem intervalWord_of_clustered [Finite V] (R : RotationSystem (contractEdge G x y))
    (d₀ : (contractEdge G x y).Dart) (hd₀ : d₀.fst = x)
    (hc : CyclicWord.Clustered (CyclicWord.xPositions (R.neighborWord d₀))
      (CyclicWord.yPositions (R.neighborWord d₀))) : IntervalWord G x y R := by
  classical
  obtain ⟨b, k, hk, hA, hnotX, hnotY⟩ := CyclicWord.clustered_interval _ _
    (R.neighborWord_cover d₀ hd₀) hc
  have hN : minimalPeriod ⇑(R.rot⁻¹) d₀ = ((contractEdge G x y).neighborSet x).ncard := by
    rw [R.minimalPeriod_rot_inv, hd₀]
  have hperiod : ∀ t, (R.rot⁻¹ ^ (t % ((contractEdge G x y).neighborSet x).ncard)) d₀ =
      (R.rot⁻¹ ^ t) d₀ := by
    intro t
    rw [← hN, coe_pow, coe_pow]
    exact iterate_mod_minimalPeriod_eq
  have hshift : ∀ j : ℕ, ((R.rot⁻¹ ^ j) ((R.rot⁻¹ ^ b.val) d₀)).snd =
      ((R.rot⁻¹ ^ (b + (j : ZMod ((contractEdge G x y).neighborSet x).ncard)).val) d₀).snd := by
    intro j
    have hs : b + (j : ZMod ((contractEdge G x y).neighborSet x).ncard) =
        ((b.val + j : ℕ) : ZMod ((contractEdge G x y).neighborSet x).ncard) := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val]
    rw [hs, ZMod.val_natCast, hperiod]
    rw [pow_add, Perm.mul_apply, ← Perm.mul_apply, ← pow_add, Nat.add_comm j b.val]
    rw [pow_add, Perm.mul_apply]
  refine Or.inr ⟨(R.rot⁻¹ ^ b.val) d₀, ?_, k, hk, ?_, ?_, ?_⟩
  · rw [R.fst_rot_inv_pow, hd₀]
  · intro j hj
    rw [hshift j]
    exact (R.mem_xPositions_neighborWord d₀).1 (hA j hj)
  · intro j hj hjN hG
    apply hnotX j hj hjN
    apply (R.mem_xPositions_neighborWord d₀).2
    rwa [← hshift j]
  · intro j hj hjk hG
    apply hnotY j hj hjk
    apply (R.mem_yPositions_neighborWord d₀).2
    rwa [← hshift j]

end RotationSystem
end Kuratowski
