import Kuratowski.Perm

/-!
# Cycles of disjoint sums of permutations

Powers and cycle membership restrict to each summand of `Perm.sumCongr f g`.
Consequently, its orbit count is `orbitCount f + orbitCount g`.
This module has no graph dependencies.
-/

namespace Kuratowski

open Equiv

section Perm

variable {α β : Type*} (f : Perm α) (g : Perm β)

theorem pow_sumCongr_inl (n : ℕ) (a : α) :
    ((Perm.sumCongr f g) ^ n) (.inl a) = .inl ((f ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Perm.mul_apply, ih, Perm.sumCongr_apply, Sum.map_inl]

theorem pow_sumCongr_inr (n : ℕ) (b : β) :
    ((Perm.sumCongr f g) ^ n) (.inr b) = .inr ((g ^ n) b) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Perm.mul_apply, ih, Perm.sumCongr_apply, Sum.map_inr]

variable [Finite α] [Finite β]

theorem sameCycle_sumCongr_inl (a b : α) :
    (Perm.sumCongr f g).SameCycle (.inl a) (.inl b) ↔ f.SameCycle a b := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [pow_sumCongr_inl] at hn
    exact ⟨n, by simpa using Sum.inl.inj hn⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by simpa only [zpow_natCast, pow_sumCongr_inl] using congrArg Sum.inl hn⟩

theorem sameCycle_sumCongr_inr (a b : β) :
    (Perm.sumCongr f g).SameCycle (.inr a) (.inr b) ↔ g.SameCycle a b := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [pow_sumCongr_inr] at hn
    exact ⟨n, by simpa using Sum.inr.inj hn⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by simpa only [zpow_natCast, pow_sumCongr_inr] using congrArg Sum.inr hn⟩

private theorem not_sameCycle_sumCongr (a : α) (b : β) :
    ¬ (Perm.sumCongr f g).SameCycle (.inl a) (.inr b) := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [pow_sumCongr_inl] at hn
  cases hn

/-- The orbit count of a disjoint sum is the sum of the orbit counts. -/
theorem orbitCount_sumCongr : orbitCount (Perm.sumCongr f g) = orbitCount f + orbitCount g := by
  let Qf := Quotient (Perm.SameCycle.setoid f)
  let Qg := Quotient (Perm.SameCycle.setoid g)
  let Q := Quotient (Perm.SameCycle.setoid (Perm.sumCongr f g))
  let F : Qf ⊕ Qg → Q := fun
    | .inl c => Quotient.map Sum.inl (fun a b h ↦ (sameCycle_sumCongr_inl f g a b).mpr h) c
    | .inr c => Quotient.map Sum.inr (fun a b h ↦ (sameCycle_sumCongr_inr f g a b).mpr h) c
  have hF : Function.Bijective F := by
    constructor
    · rintro (a | a) (b | b) h
      all_goals
        induction a using Quotient.inductionOn with | h a => ?_
        induction b using Quotient.inductionOn with | h b => ?_
      · exact congrArg Sum.inl (Quotient.sound
          ((sameCycle_sumCongr_inl f g a b).mp (Quotient.exact h)))
      · exact (not_sameCycle_sumCongr f g a b (Quotient.exact h)).elim
      · exact (not_sameCycle_sumCongr f g b a (Quotient.exact h).symm).elim
      · exact congrArg Sum.inr (Quotient.sound
          ((sameCycle_sumCongr_inr f g a b).mp (Quotient.exact h)))
    · intro q
      induction q using Quotient.inductionOn with
      | h x =>
        cases x with
        | inl a => exact ⟨.inl ⟦a⟧, rfl⟩
        | inr b => exact ⟨.inr ⟦b⟧, rfl⟩
  unfold orbitCount
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_sum]

end Perm

/-- A cycle in the left summand remains a cycle in the disjoint sum. -/
theorem sameCycle_sumCongr_left {α β : Type*} [Finite α] [Finite β]
    (f : Perm α) (g : Perm β) {a b : α} (h : f.SameCycle a b) :
    (Perm.sumCongr f g).SameCycle (.inl a) (.inl b) :=
  (sameCycle_sumCongr_inl f g a b).2 h

/-- A cycle in the right summand remains a cycle in the disjoint sum. -/
theorem sameCycle_sumCongr_right {α β : Type*} [Finite α] [Finite β]
    (f : Perm α) (g : Perm β) {a b : β} (h : g.SameCycle a b) :
    (Perm.sumCongr f g).SameCycle (.inr a) (.inr b) :=
  (sameCycle_sumCongr_inr f g a b).2 h

/-- Points in different summands never lie in the same cycle. -/
theorem not_sameCycle_sumCongr_cross {α β : Type*} [Finite α] [Finite β]
    (f : Perm α) (g : Perm β) (a : α) (b : β) :
    ¬ (Perm.sumCongr f g).SameCycle (.inl a) (.inr b) :=
  not_sameCycle_sumCongr f g a b

end Kuratowski
