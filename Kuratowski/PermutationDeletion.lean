import Kuratowski.Perm

/-!
# 순열 위에서 역다트 한 쌍 지우기

평행 변을 잠시 유지하는 수술의 중간 상태는 단순 그래프의 다트가 아닐 수 있다. 이 파일은 임의의
유한 타입에서 두 점을 잘라 내는 식과 순환 수를 다루며, 그래프의 회전 체계라는 가정을 쓰지 않는다.

`cut_pair_comp`는 회전 순열에서 두 역다트를 잘라 낸 결과의 면 순열 식이고,
`orbitCount_cut_pair_face`는 삭제할 두 다트가 서로 다른 면 순환에 있을 때 순환 수가 하나 줄어듦을
보인다. 전제의 비고정점 조건과 역다트 교환 조건은 호출자가 증명해야 한다.
-/

open Equiv Equiv.Perm
namespace Kuratowski.PermutationDeletion
variable {α : Type*} [DecidableEq α]

lemma cut_pair_comp (ρ σ : Perm α) (hσ : Function.Involutive σ) {a b x : α}
    (hab : a ≠ b) (hσa : σ a = b) (hσb : σ b = a) (hxa : x ≠ a) (hxb : x ≠ b) :
    cut (cut ρ a) b (σ x) = cut (cut (ρ * σ * swap a b) a) b x := by
  have hs1 : σ x ≠ b := fun h ↦ hxa (hσ.injective (h.trans hσa.symm))
  have hs2 : σ x ≠ a := fun h ↦ hxb (hσ.injective (h.trans hσb.symm))
  have hψx : (ρ * σ * swap a b) x = ρ (σ x) := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxb, Perm.mul_apply]
  have hψa : (ρ * σ * swap a b) a = ρ a := by
    rw [Perm.mul_apply, swap_apply_left, Perm.mul_apply, hσb]
  have hψb : (ρ * σ * swap a b) b = ρ b := by
    rw [Perm.mul_apply, swap_apply_right, Perm.mul_apply, hσa]
  rw [cut_apply_of_ne _ hs1, cut_apply_of_ne _ hxb, cut_apply_of_ne _ hs2,
    cut_apply_of_ne _ hxa, cut_apply_of_ne _ hab.symm, cut_apply_of_ne _ hab.symm, hψx, hψa, hψb]

omit [DecidableEq α] in
lemma pair_pred (f : Perm α) {a b : α} (ha : f a = a) (hb : f b = b) (x : α) :
    (f x ≠ a ∧ f x ≠ b) ↔ (x ≠ a ∧ x ≠ b) := by
  constructor
  · rintro ⟨hxa, hxb⟩
    exact ⟨fun h ↦ hxa (h ▸ ha), fun h ↦ hxb (h ▸ hb)⟩
  · rintro ⟨hxa, hxb⟩
    exact ⟨fun h ↦ hxa (f.injective (h.trans ha.symm)),
      fun h ↦ hxb (f.injective (h.trans hb.symm))⟩

lemma cut_pair_left (f : Perm α) {a b : α} (hab : a ≠ b) : cut (cut f a) b a = a := by
  rw [cut_apply_of_ne _ hab, cut_apply_self]
  simp [hab]

lemma orbitCount_cut_pair_restrict [Finite α] (f : Perm α) {a b : α} (hab : a ≠ b)
    (ha : f a ≠ a) (hb : cut f a b ≠ b) :
    orbitCount ((cut (cut f a) b).subtypePerm (p := fun x ↦ x ≠ a ∧ x ≠ b)
      (pair_pred _ (cut_pair_left f hab) (cut_apply_self _ _))) = orbitCount f := by
  have hleft := cut_pair_left f hab
  have hright := cut_apply_self (cut f a) b
  have h1 := orbitCount_eq_subtypePerm_add (cut (cut f a) b) (fun x ↦ x ≠ a ∧ x ≠ b)
    (pair_pred _ hleft hright) (by
      intro x hx
      by_cases hxa : x = a
      · simpa [hxa] using hleft
      · have hxb : x = b := by
          by_contra hxb
          exact hx ⟨hxa, hxb⟩
        simp [hxb])
  have h2 : Nat.card {x : α // ¬(x ≠ a ∧ x ≠ b)} = 2 := by
    have hs : {x : α | ¬(x ≠ a ∧ x ≠ b)} = {a, b} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    change Nat.card ↥{x : α | ¬(x ≠ a ∧ x ≠ b)} = 2
    rw [Nat.card_coe_set_eq, hs, Set.ncard_pair hab]
  have h3 := orbitCount_cut f a
  have h4 := orbitCount_cut (cut f a) b
  simp only [ha, hb, ↓reduceIte] at h3 h4
  omega

lemma orbitCount_cut_pair_face [Finite α] (ρ σ : Perm α) {a b : α} (hab : a ≠ b)
    (hσa : σ a = b) (hσb : σ b = a) (hρa : ρ a ≠ a) (hρb : ρ b ≠ b)
    (hρba : ρ b ≠ a) (hn : ¬ (ρ * σ).SameCycle a b) :
    orbitCount ((cut (cut (ρ * σ * swap a b) a) b).subtypePerm
      (p := fun x ↦ x ≠ a ∧ x ≠ b)
      (pair_pred _ (cut_pair_left _ hab) (cut_apply_self _ _))) + 1 = orbitCount (ρ * σ) := by
  have hψa : (ρ * σ * swap a b) a = ρ a := by
    rw [Perm.mul_apply, swap_apply_left, Perm.mul_apply, hσb]
  have hψb : (ρ * σ * swap a b) b = ρ b := by
    rw [Perm.mul_apply, swap_apply_right, Perm.mul_apply, hσa]
  have ha : (ρ * σ * swap a b) a ≠ a := by rw [hψa]; exact hρa
  have hb : cut (ρ * σ * swap a b) a b ≠ b := by
    rw [cut_apply_of_ne _ hab.symm, hψb]
    simp only [hρba, ↓reduceIte]
    exact hρb
  rw [orbitCount_cut_pair_restrict _ hab ha hb]
  exact orbitCount_mul_swap_of_not_sameCycle hn

lemma orbitCount_two_swaps [Finite α] (f : Perm α) {a b c d : α}
    (hn : ¬ f.SameCycle a b) (hc : f.SameCycle c a) (hd : f.SameCycle d b) (hcd : c ≠ d) :
    orbitCount (f * swap a b * swap c d) = orbitCount f := by
  have hj := sameCycle_mul_swap_of_not hn
  have hsame : (f * swap a b).SameCycle c d :=
    (hj.mul_swap_of_sameCycle hc).trans (hj.trans (hj.mul_swap_of_sameCycle hd).symm)
  have h1 := orbitCount_mul_swap_of_not_sameCycle hn
  have h2 := orbitCount_mul_swap_of_sameCycle hcd hsame
  omega

omit [DecidableEq α] in
lemma not_sameCycle_of_two_cycle [Finite α] (f : Perm α) {a b c : α}
    (ha : f a = b) (hb : f b = a) (hca : c ≠ a) (hcb : c ≠ b) : ¬ f.SameCycle a c := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hpow : ∀ n : ℕ, (f ^ n) a = a ∨ (f ^ n) a = b := by
    intro n
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      rcases ih with h | h
      · exact Or.inr (by rw [h, ha])
      · exact Or.inl (by rw [h, hb])
  rcases hpow n with h | h
  · exact hca (hn.symm.trans h)
  · exact hcb (hn.symm.trans h)

lemma swaps_comp_involution (ρ σ : Perm α) (hσ : Function.Involutive σ) (p a b q : α) :
    (ρ * swap p a * swap b q) * σ =
      (ρ * σ) * swap (σ p) (σ a) * swap (σ b) (σ q) := by
  have hs (u v x : α) : swap u v (σ x) = σ (swap (σ u) (σ v) x) := by
    have h := σ.injective.map_swap (σ u) (σ v) x
    simpa only [hσ u, hσ v] using h.symm
  ext x
  simp only [Perm.mul_apply, hs]

end Kuratowski.PermutationDeletion
