import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# 순열의 순환 수

면의 개수는 면 순열의 순환(궤도) 수다. 변을 지우거나 차수 2인 꼭짓점을 펴는 수술은
면 순열에 호환(transposition)을 몇 번 곱하는 것으로 쓸 수 있으므로, 순환 수가 어떻게
바뀌는지만 알면 된다. 핵심은 다음 사실이다.

* `a`, `b`가 `f`의 서로 다른 순환에 있으면 `f * swap a b`에서 두 순환이 합쳐진다 (`-1`).
* `a ≠ b`가 같은 순환에 있으면 그 순환이 둘로 갈라진다 (`+1`).

갈라지는 쪽은 합쳐지는 쪽에 `f = (f * swap a b) * swap a b`를 적용해 얻는다. 이때
`f * swap a b`에서 `a`, `b`가 다른 순환에 있다는 것은 부호(sign)로 보인다.
-/

namespace Kuratowski

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α]

/-- 순열의 순환 수 (고정점도 순환 하나로 센다). -/
noncomputable def orbitCount (f : Perm α) : ℕ := Nat.card (Quotient (SameCycle.setoid f))

/-! ## 구역 보조정리 -/

omit [DecidableEq α] in
/-- 한 걸음마다 `s`-동치이거나 두 끝이 모두 "`a` 또는 `b`와 `s`-동치인 구역"에 있으면,
여러 걸음 뒤에도 그렇다. -/
lemma reflTransGen_zone {r s : α → α → Prop} (hs : Equivalence s) (a b : α)
    (h : ∀ x z, r x z → s x z ∨ ((s x a ∨ s x b) ∧ (s z a ∨ s z b))) {x y : α}
    (hxy : Relation.ReflTransGen r x y) :
    s x y ∨ ((s x a ∨ s x b) ∧ (s y a ∨ s y b)) := by
  induction hxy with
  | refl => exact Or.inl (hs.refl x)
  | @tail y z _ hyz ih =>
    have zone : ∀ {p q}, s p q → (s q a ∨ s q b) → (s p a ∨ s p b) := fun hpq hq =>
      hq.imp (hs.trans hpq) (hs.trans hpq)
    rcases ih with hxy | ⟨hx, hy⟩ <;> rcases h y z hyz with hyz' | ⟨hy', hz⟩
    · exact Or.inl (hs.trans hxy hyz')
    · exact Or.inr ⟨zone hxy hy', hz⟩
    · exact Or.inr ⟨hx, zone (hs.symm hyz') hy⟩
    · exact Or.inr ⟨hx, hz⟩

omit [DecidableEq α] in
lemma reflTransGen_of_sameCycle [Finite α] {f : Perm α} {x y : α} (h : SameCycle f x y) :
    Relation.ReflTransGen (fun p q => q = f p) x y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact .refl
  | succ n ih => exact ih.tail (by rw [pow_succ', Perm.mul_apply])

/-- `f * swap a b`의 순환은 `f`의 순환이거나, `a`·`b`의 `f`-순환에 걸쳐 있다. -/
lemma sameCycle_mul_swap_zone [Finite α] {f : Perm α} {a b x y : α}
    (h : SameCycle (f * swap a b) x y) :
    SameCycle f x y ∨ ((SameCycle f x a ∨ SameCycle f x b) ∧ (SameCycle f y a ∨ SameCycle f y b)) := by
  refine reflTransGen_zone (SameCycle.setoid f).iseqv a b (fun p q hpq => ?_)
    (reflTransGen_of_sameCycle h)
  subst hpq
  rw [Perm.mul_apply]
  by_cases hpa : p = a
  · subst hpa
    rw [swap_apply_left]
    exact Or.inr ⟨Or.inl (SameCycle.refl _ _),
      Or.inr (sameCycle_apply_left.2 (SameCycle.refl _ _))⟩
  by_cases hpb : p = b
  · subst hpb
    rw [swap_apply_right]
    exact Or.inr ⟨Or.inr (SameCycle.refl _ _),
      Or.inl (sameCycle_apply_left.2 (SameCycle.refl _ _))⟩
  rw [swap_apply_of_ne_of_ne hpa hpb]
  exact Or.inl (sameCycle_apply_right.2 (SameCycle.refl _ _))

/-! ## 합쳐지는 경우 -/

/-- `f * swap a b`에서 `a`, `b`가 같은 순환에 있으면 `f`의 순환은 `f * swap a b`의
순환 안에 들어간다. -/
lemma _root_.Equiv.Perm.SameCycle.mul_swap_of_sameCycle [Finite α] {f : Perm α} {a b : α}
    (hab : SameCycle (f * swap a b) a b) {x y : α} (h : SameCycle f x y) :
    SameCycle (f * swap a b) x y := by
  have step : ∀ p, SameCycle (f * swap a b) p (f p) := by
    intro p
    by_cases hpa : p = a
    · subst hpa
      have : f p = (f * swap p b) b := by simp [Perm.mul_apply]
      rw [this]
      exact hab.trans (sameCycle_apply_right.2 (SameCycle.refl _ _))
    by_cases hpb : p = b
    · subst hpb
      have : f p = (f * swap a p) a := by simp [Perm.mul_apply]
      rw [this]
      exact hab.symm.trans (sameCycle_apply_right.2 (SameCycle.refl _ _))
    have : f p = (f * swap a b) p := by simp [Perm.mul_apply, swap_apply_of_ne_of_ne hpa hpb]
    rw [this]
    exact sameCycle_apply_right.2 (SameCycle.refl _ _)
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact SameCycle.refl _ _
  | succ n ih => rw [pow_succ', Perm.mul_apply]; exact ih.trans (step _)

/-- `a`, `b`가 `f`의 서로 다른 순환에 있으면 `f * swap a b`에서는 같은 순환에 있다. -/
lemma sameCycle_mul_swap_of_not [Finite α] {f : Perm α} {a b : α} (hab : ¬ SameCycle f a b) :
    SameCycle (f * swap a b) a b := by
  classical
  have hex : ∃ n, (f ^ n) (f b) = b :=
    (sameCycle_apply_left.2 (SameCycle.refl f b)).exists_nat_pow_eq
  set n := Nat.find hex with hn
  have key : ∀ k ≤ n, ((f * swap a b) ^ k) ((f * swap a b) a) = (f ^ k) (f b) := by
    intro k
    induction k with
    | zero => intro _; simp [Perm.mul_apply]
    | succ k ih =>
      intro hk
      rw [pow_succ', Perm.mul_apply, ih (by omega), pow_succ', Perm.mul_apply]
      have hb : (f ^ k) (f b) ≠ b := Nat.find_min hex (by omega)
      have ha : (f ^ k) (f b) ≠ a := by
        intro h
        have : SameCycle f ((f ^ k) (f b)) b :=
          sameCycle_pow_left.2 (sameCycle_apply_left.2 (SameCycle.refl f b))
        rw [h] at this
        exact hab this
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne ha hb]
  refine ⟨((n + 1 : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, pow_succ, Perm.mul_apply, key n le_rfl]
  exact Nat.find_spec hex

lemma sameCycle_iff_of_mul_swap_not [Finite α] {f : Perm α} {a b : α}
    (hab : ¬ SameCycle f a b) {x y : α} :
    SameCycle (f * swap a b) x y ↔
      SameCycle f x y ∨ (SameCycle f x a ∧ SameCycle f y b) ∨ (SameCycle f x b ∧ SameCycle f y a) := by
  have hψ := sameCycle_mul_swap_of_not hab
  constructor
  · intro h
    rcases sameCycle_mul_swap_zone h with h | ⟨hx | hx, hy | hy⟩
    · exact Or.inl h
    · exact Or.inl (hx.trans hy.symm)
    · exact Or.inr (Or.inl ⟨hx, hy⟩)
    · exact Or.inr (Or.inr ⟨hx, hy⟩)
    · exact Or.inl (hx.trans hy.symm)
  · rintro (h | ⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact hψ.mul_swap_of_sameCycle h
    · exact (hψ.mul_swap_of_sameCycle hx).trans (hψ.trans (hψ.mul_swap_of_sameCycle hy).symm)
    · exact (hψ.mul_swap_of_sameCycle hx).trans
        (hψ.symm.trans (hψ.mul_swap_of_sameCycle hy).symm)

/-- **합쳐짐**: `a`, `b`가 `f`의 서로 다른 순환에 있으면 순환 수가 하나 준다. -/
theorem orbitCount_mul_swap_of_not_sameCycle [Finite α] {f : Perm α} {a b : α}
    (hab : ¬ SameCycle f a b) : orbitCount (f * swap a b) + 1 = orbitCount f := by
  classical
  have hψ := sameCycle_mul_swap_of_not hab
  set ψ := f * swap a b
  let Qf := Quotient (SameCycle.setoid f)
  let Qψ := Quotient (SameCycle.setoid ψ)
  have := Fintype.ofFinite α
  let π : Qf → Qψ := Quotient.map id fun x y (h : SameCycle f x y) =>
    (hψ.mul_swap_of_sameCycle h : SameCycle ψ x y)
  let F : Qf → Option Qψ := fun c => if c = ⟦b⟧ then none else some (π c)
  have hF : Function.Bijective F := by
    constructor
    · intro c₁ c₂ h
      induction c₁ using Quotient.inductionOn with | h x => ?_
      induction c₂ using Quotient.inductionOn with | h y => ?_
      by_cases hx : (⟦x⟧ : Qf) = ⟦b⟧ <;> by_cases hy : (⟦y⟧ : Qf) = ⟦b⟧
      · rw [hx, hy]
      · simp [F, hx, hy] at h
      · simp [F, hx, hy] at h
      · have h₁ : (⟦x⟧ : Qψ) = ⟦y⟧ := by simpa [F, hx, hy, π] using h
        have h' : SameCycle ψ x y := Quotient.exact h₁
        apply Quotient.sound
        change SameCycle f x y
        rcases (sameCycle_iff_of_mul_swap_not hab).1 h' with h'' | ⟨_, hyb⟩ | ⟨hxb, _⟩
        · exact h''
        · exact absurd (Quotient.sound hyb) hy
        · exact absurd (Quotient.sound hxb) hx
    · intro o
      rcases o with _ | q
      · exact ⟨⟦b⟧, by simp [F]⟩
      · induction q using Quotient.inductionOn with | h x => ?_
        by_cases hx : (⟦x⟧ : Qf) = ⟦b⟧
        · have ha : (⟦a⟧ : Qf) ≠ ⟦b⟧ := fun h => hab (Quotient.exact h)
          refine ⟨⟦a⟧, ?_⟩
          have h₂ : (⟦a⟧ : Qψ) = ⟦x⟧ :=
            Quotient.sound (hψ.trans (hψ.mul_swap_of_sameCycle (Quotient.exact hx).symm) :
              SameCycle ψ a x)
          simp only [F, ha, ↓reduceIte]
          exact congrArg some h₂
        · exact ⟨⟦x⟧, by simp [F, hx, π]⟩
  have := Nat.card_eq_of_bijective F hF
  unfold orbitCount
  rw [this, Finite.card_option]

/-! ## 갈라지는 경우 -/

lemma not_sameCycle_mul_swap_of_sameCycle [Finite α] {f : Perm α} {a b : α} (hne : a ≠ b)
    (hab : SameCycle f a b) : ¬ SameCycle (f * swap a b) a b := by
  classical
  have := Fintype.ofFinite α
  intro hψ
  set ψ := f * swap a b with hψdef
  have hf : f = ψ * swap a b := by rw [hψdef, mul_swap_mul_self]
  -- 두 순열의 "같은 순환" 관계가 같다.
  have iff : ∀ x y, SameCycle f x y ↔ SameCycle ψ x y := by
    intro x y
    constructor
    · exact hψ.mul_swap_of_sameCycle
    · intro h
      have hab' : SameCycle (ψ * swap a b) a b := by rwa [← hf]
      have := hab'.mul_swap_of_sameCycle h
      rwa [← hf] at this
  have hfa : f a ≠ a := fun h => hne (hab.eq_of_left h)
  have hψa : ψ a ≠ a := fun h => hne (hψ.eq_of_left h)
  have hcyc : ψ.cycleOf a = f.cycleOf a * swap a b := by
    ext x
    rw [Perm.mul_apply, cycleOf_apply, cycleOf_apply]
    by_cases hxa : x = a
    · rw [hxa]
      simp [hψdef, Perm.mul_apply, SameCycle.refl, hab]
    by_cases hxb : x = b
    · rw [hxb]
      have hψ' : (f * swap a b).SameCycle a b := hψ
      simp [hψdef, Perm.mul_apply, SameCycle.refl, hψ']
    rw [swap_apply_of_ne_of_ne hxa hxb]
    by_cases hs : SameCycle f a x
    · simp only [(iff a x).1 hs, hs, ↓reduceIte]
      simp [hψdef, Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxb]
    · have hs' : ¬ ψ.SameCycle a x := fun h => hs ((iff a x).2 h)
      simp [hs, hs']
  have hsupp : (ψ.cycleOf a).support = (f.cycleOf a).support := by
    ext y
    rw [mem_support_cycleOf_iff' hψa, mem_support_cycleOf_iff' hfa, iff]
  have h1 := (isCycle_cycleOf ψ hψa).sign
  have h2 := (isCycle_cycleOf f hfa).sign
  rw [hsupp, ← h2, hcyc, sign_mul, sign_swap hne] at h1
  rcases Int.units_eq_one_or (sign (f.cycleOf a)) with h | h <;> rw [h] at h1 <;> revert h1 <;>
    decide

/-- **갈라짐**: `a ≠ b`가 `f`의 같은 순환에 있으면 순환 수가 하나 는다. -/
theorem orbitCount_mul_swap_of_sameCycle [Finite α] {f : Perm α} {a b : α} (hne : a ≠ b)
    (hab : SameCycle f a b) : orbitCount (f * swap a b) = orbitCount f + 1 := by
  have h := orbitCount_mul_swap_of_not_sameCycle (not_sameCycle_mul_swap_of_sameCycle hne hab)
  rw [mul_swap_mul_self] at h
  exact h.symm

/-! ## 점 하나를 순환에서 잘라 내기 -/

/-- `a`를 그 순환에서 잘라 내어 고정점으로 만든다: `… → p → a → q → …`를
`… → p → q → …`와 `a → a`로 바꾼다. -/
def cut (f : Perm α) (a : α) : Perm α := f * swap (f⁻¹ a) a

@[simp] lemma cut_apply_self (f : Perm α) (a : α) : cut f a a = a := by
  simp [cut, Perm.mul_apply]

lemma cut_apply_of_ne (f : Perm α) {a x : α} (hx : x ≠ a) :
    cut f a x = if f x = a then f a else f x := by
  unfold cut
  rw [Perm.mul_apply]
  split_ifs with h
  · have : x = f⁻¹ a := by rw [← h]; simp
    rw [this, swap_apply_left]
  · have : x ≠ f⁻¹ a := by rintro rfl; exact h (by simp)
    rw [swap_apply_of_ne_of_ne this hx]

/-- 함수 `g`의 값을 보존하는 순열을 잘라도 `g`의 값은 보존된다. -/
lemma cut_preserves {β : Type*} (f : Perm α) (a : α) (g : α → β) (hg : ∀ x, g (f x) = g x)
    (x : α) : g (cut f a x) = g x := by
  by_cases hx : x = a
  · subst hx; simp
  rw [cut_apply_of_ne f hx]
  split_ifs with h
  · rw [hg, ← h, hg]
  · exact hg x

lemma orbitCount_cut [Finite α] (f : Perm α) (a : α) :
    orbitCount (cut f a) = orbitCount f + if f a = a then 0 else 1 := by
  split_ifs with h
  · have : f⁻¹ a = a := by rw [Perm.inv_eq_iff_eq, h]
    simp [cut, this, ← Perm.one_def]
  · have hne : f⁻¹ a ≠ a := fun h' => h (by rw [Perm.inv_eq_iff_eq] at h'; exact h'.symm)
    exact orbitCount_mul_swap_of_sameCycle hne
      (sameCycle_apply_left.1 (by rw [show f (f⁻¹ a) = a by simp]))

/-- `a`가 아닌 두 점이 `f`의 같은 순환에 있으면 `cut f a`에서도 같은 순환에 있다. -/
lemma sameCycle_cut [Finite α] {f : Perm α} {a x y : α} (hx : x ≠ a) (hy : y ≠ a)
    (h : SameCycle f x y) : SameCycle (cut f a) x y := by
  by_cases hfa : f a = a
  · have : f⁻¹ a = a := by rw [Perm.inv_eq_iff_eq, hfa]
    simpa [Kuratowski.cut, this, ← Perm.one_def] using h
  have hf : f = cut f a * swap (f⁻¹ a) a := by rw [Kuratowski.cut, mul_swap_mul_self]
  rw [hf] at h
  rcases sameCycle_mul_swap_zone h with h | ⟨hx' | hx', hy' | hy'⟩
  · exact h
  · exact hx'.trans hy'.symm
  · exact absurd (hy'.eq_of_right (cut_apply_self f a)) hy
  · exact absurd (hx'.eq_of_right (cut_apply_self f a)) hx
  · exact absurd (hx'.eq_of_right (cut_apply_self f a)) hx

/-! ## 고정점 떼어 내기와 옮기기 -/

omit [DecidableEq α] in
/-- `p`를 만족하지 않는 점은 모두 고정점이면, 순환 수는 `p` 위로 제한한 순열의 순환 수에
고정점 수를 더한 것이다. -/
lemma orbitCount_eq_subtypePerm_add [Finite α] (f : Perm α) (p : α → Prop)
    (hp : ∀ x, p (f x) ↔ p x) (hfix : ∀ x, ¬ p x → f x = x) :
    orbitCount f = orbitCount (f.subtypePerm hp) + Nat.card {x // ¬ p x} := by
  classical
  let Qf := Quotient (SameCycle.setoid f)
  let Qs := Quotient (SameCycle.setoid (f.subtypePerm hp))
  let F : Qs ⊕ {x // ¬ p x} → Qf := fun
    | .inl c => Quotient.map Subtype.val (fun x y h => sameCycle_subtypePerm.1 h) c
    | .inr x => ⟦x.1⟧
  have hF : Function.Bijective F := by
    constructor
    · rintro (c₁ | ⟨y₁, hy₁⟩) (c₂ | ⟨y₂, hy₂⟩) h
      · induction c₁ using Quotient.inductionOn with | h x => ?_
        induction c₂ using Quotient.inductionOn with | h y => ?_
        have h₁ : (⟦x.1⟧ : Qf) = ⟦y.1⟧ := h
        exact congrArg Sum.inl (Quotient.sound (sameCycle_subtypePerm.2 (Quotient.exact h₁)))
      · induction c₁ using Quotient.inductionOn with | h x => ?_
        have h₁ : (⟦x.1⟧ : Qf) = ⟦y₂⟧ := h
        have h' : SameCycle f x.1 y₂ := Quotient.exact h₁
        have := h'.symm.eq_of_left (hfix y₂ hy₂)
        exact (hy₂ (by rw [this]; exact x.2)).elim
      · induction c₂ using Quotient.inductionOn with | h x => ?_
        have h₁ : (⟦y₁⟧ : Qf) = ⟦x.1⟧ := h
        have h' : SameCycle f y₁ x.1 := Quotient.exact h₁
        have := h'.eq_of_left (hfix y₁ hy₁)
        exact (hy₁ (by rw [this]; exact x.2)).elim
      · have h₁ : (⟦y₁⟧ : Qf) = ⟦y₂⟧ := h
        have h' : SameCycle f y₁ y₂ := Quotient.exact h₁
        have := h'.eq_of_left (hfix y₁ hy₁)
        subst this
        rfl
    · intro c
      induction c using Quotient.inductionOn with | h x => ?_
      by_cases hx : p x
      · exact ⟨.inl ⟦⟨x, hx⟩⟧, rfl⟩
      · exact ⟨.inr ⟨x, hx⟩, rfl⟩
  unfold orbitCount
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_sum]

omit [DecidableEq α] in
/-- 순열을 일대일 대응으로 옮겨도 "같은 순환" 관계는 그대로다. -/
lemma sameCycle_permCongr_iff {β : Type*} [Finite α] (e : α ≃ β) (σ : Perm α)
    (a b : α) : (e.permCongr σ).SameCycle (e a) (e b) ↔ σ.SameCycle a b := by
  have hpow : ∀ (n : ℕ) x, ((e.permCongr σ) ^ n) x = e ((σ ^ n) (e.symm x)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro x; simp [pow_succ, Perm.mul_apply, ih, Equiv.permCongr_apply]
  have : Finite β := .of_equiv α e
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [hpow, e.symm_apply_apply] at hn
    exact ⟨n, by simpa using e.injective hn⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by simp [hpow, hn]⟩

omit [DecidableEq α] in
lemma orbitCount_permCongr {β : Type*} [Finite α] (e : α ≃ β) (σ : Perm α) :
    orbitCount (e.permCongr σ) = orbitCount σ := by
  unfold orbitCount
  refine (Nat.card_congr (Quotient.congr e fun a b => ?_)).symm
  change σ.SameCycle a b ↔ (e.permCongr σ).SameCycle (e a) (e b)
  rw [sameCycle_permCongr_iff]

end Kuratowski
