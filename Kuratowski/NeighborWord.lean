import Kuratowski.VertexSplit
import Kuratowski.CyclicWord
import Kuratowski.DelVertexFace
import Mathlib.Tactic.Abel

/-!
# 순환 단어 분류와 실제 회전의 구간 조건

`Clustered`인 단어가 모든 위치를 `X` 또는 `Y`로 덮으면 시작점과 절단 위치를 고를 수 있다.
수축 회전의 역순 이웃 열에서 읽은 단어에 이를 적용하면 꼭짓점 나누기의 `IntervalWord`를 얻는다.
또 증가하는 자연수 위치 열이 열린 순환 순서를 보존함을 증명한다. J2의 위치 열로 교대 배치를 실제
사이클에 옮길 때 쓴다. 정규식 라이브러리를 쓰는 대신 유한 순환 위치의 명시적 구간 조건을 다룬다.
-/

namespace Kuratowski.CyclicWord

/-- 서로 다른 끝점의 닫힌 호는 끝점과 열린 호의 합이다. -/
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

/-- 닫힌 호의 모듈러 거리 판정. 두 끝점이 다르다는 조건이 필요하다. -/
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

/-- `X`와 `Y`가 모든 위치를 덮으면, Clustered인 단어는 시작점과 한 절단 위치로 표현된다. -/
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

/-- 증가하는 위치 열은 열린 순환 순서를 보존한다. -/
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

/-- 수축 회전의 역순 이웃 열에서 원래 두 점의 인접 여부를 읽은 단어. -/
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

/-- 순환 단어 분류의 첫 경우는 실제 회전의 구간 조건을 준다. -/
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
