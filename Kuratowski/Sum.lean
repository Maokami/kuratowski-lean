import Kuratowski.Map
import Kuratowski.Euler
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# 서로소 그래프의 평면 회전 체계

먼저 서로소 타입 합 위의 그래프를 다루고, 지지 집합이 서로소인 고정 타입 위의 합집합으로 옮긴다.
-/

namespace Kuratowski

open SimpleGraph Equiv

section Perm

variable {α β : Type*} (f : Perm α) (g : Perm β)

private theorem pow_sumCongr_inl (n : ℕ) (a : α) :
    ((Perm.sumCongr f g) ^ n) (.inl a) = .inl ((f ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Perm.mul_apply, ih, Perm.sumCongr_apply, Sum.map_inl]

private theorem pow_sumCongr_inr (n : ℕ) (b : β) :
    ((Perm.sumCongr f g) ^ n) (.inr b) = .inr ((g ^ n) b) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Perm.mul_apply, ih, Perm.sumCongr_apply, Sum.map_inr]

variable [Finite α] [Finite β]

private theorem sameCycle_sumCongr_inl (a b : α) :
    (Perm.sumCongr f g).SameCycle (.inl a) (.inl b) ↔ f.SameCycle a b := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [pow_sumCongr_inl] at hn
    exact ⟨n, by simpa using Sum.inl.inj hn⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by simpa only [zpow_natCast, pow_sumCongr_inl] using congrArg Sum.inl hn⟩

private theorem sameCycle_sumCongr_inr (a b : β) :
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

/-- 서로소 합에서 각 쪽의 순열이 따로 작용하면 순환 수가 더해진다. -/
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

variable {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)

/-- 그래프 서로소 합의 다트는 각 그래프의 다트의 서로소 합이다. -/
def dartEquivSum : G.Dart ⊕ H.Dart ≃ (G ⊕g H).Dart where
  toFun
    | .inl d => ⟨(.inl d.fst, .inl d.snd), d.adj⟩
    | .inr d => ⟨(.inr d.fst, .inr d.snd), d.adj⟩
  invFun
    | ⟨(.inl u, .inl v), h⟩ => .inl ⟨(u, v), h⟩
    | ⟨(.inr u, .inr v), h⟩ => .inr ⟨(u, v), h⟩
    | ⟨(.inl _, .inr _), h⟩ => False.elim (by simp at h)
    | ⟨(.inr _, .inl _), h⟩ => False.elim (by simp at h)
  left_inv := by rintro (⟨⟨u, v⟩, h⟩ | ⟨⟨u, v⟩, h⟩) <;> rfl
  right_inv := by
    rintro ⟨⟨u | u, v | v⟩, h⟩ <;> first | rfl | simp at h

namespace RotationSystem

variable [Finite V] [Finite W]

/-- 각 쪽의 꼭짓점에서 회전을 독립적으로 수행한다. -/
def sum (R : RotationSystem G) (S : RotationSystem H) : RotationSystem (G ⊕g H) where
  rot := (dartEquivSum G H).permCongr (Perm.sumCongr R.rot S.rot)
  fst_rot d := by
    obtain ⟨d, rfl⟩ := (dartEquivSum G H).surjective d
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    cases d with
    | inl d => exact congrArg Sum.inl (R.fst_rot d)
    | inr d => exact congrArg Sum.inr (S.fst_rot d)
  sameCycle_rot d d' hd := by
    obtain ⟨d, rfl⟩ := (dartEquivSum G H).surjective d
    obtain ⟨d', rfl⟩ := (dartEquivSum G H).surjective d'
    rw [sameCycle_permCongr_iff]
    cases d with
    | inl d =>
      cases d' with
      | inl d' =>
        exact (sameCycle_sumCongr_inl R.rot S.rot d d').mpr
          (R.sameCycle_rot d d' (Sum.inl.inj hd))
      | inr d' =>
        change Sum.inl _ = Sum.inr _ at hd
        cases hd
    | inr d =>
      cases d' with
      | inl d' =>
        change Sum.inr _ = Sum.inl _ at hd
        cases hd
      | inr d' =>
        exact (sameCycle_sumCongr_inr R.rot S.rot d d').mpr
          (S.sameCycle_rot d d' (Sum.inr.inj hd))

/-- 서로소 합의 면 순열은 두 면 순열의 서로소 합이다. -/
theorem sum_facePerm (R : RotationSystem G) (S : RotationSystem H) :
    (R.sum G H S).facePerm =
      (dartEquivSum G H).permCongr (Perm.sumCongr R.facePerm S.facePerm) := by
  ext1 d
  obtain ⟨d, rfl⟩ := (dartEquivSum G H).surjective d
  rcases d with ⟨⟨u, v⟩, h⟩ | ⟨⟨u, v⟩, h⟩ <;> rfl

/-- 면 순환 수는 서로소 합에서 더해진다. -/
theorem orbitCount_sum_facePerm (R : RotationSystem G) (S : RotationSystem H) :
    orbitCount (R.sum G H S).facePerm = orbitCount R.facePerm + orbitCount S.facePerm := by
  rw [sum_facePerm, orbitCount_permCongr, orbitCount_sumCongr]

end RotationSystem

private theorem reachable_sum_inl_iff (u v : V) :
    (G ⊕g H).Reachable (.inl u) (.inl v) ↔ G.Reachable u v := by
  constructor
  · rintro ⟨p⟩
    have key : ∀ {a b : V ⊕ W} (q : (G ⊕g H).Walk a b),
        ∀ c, a = .inl c → ∃ d, b = .inl d ∧ G.Reachable c d := by
      intro a b q
      induction q with
      | nil => intro c hc; exact ⟨c, hc, .refl c⟩
      | @cons a b t h q ih =>
        intro c hc
        subst a
        cases b with
        | inl b =>
          obtain ⟨d, hd, hbd⟩ := ih b rfl
          exact ⟨d, hd, (show G.Adj c b by simpa using h).reachable.trans hbd⟩
        | inr b => simp at h
    obtain ⟨d, hd, hud⟩ := key p u rfl
    cases Sum.inl.inj hd
    exact hud
  · intro h
    exact h.map (Embedding.sumInl : G ↪g G ⊕g H).toHom

private theorem reachable_sum_inr_iff (u v : W) :
    (G ⊕g H).Reachable (.inr u) (.inr v) ↔ H.Reachable u v := by
  constructor
  · intro h
    exact (reachable_sum_inl_iff H G u v).mp
      (h.map (Iso.sumComm : G ⊕g H ≃g H ⊕g G).toHom)
  · intro h
    exact h.map (Embedding.sumInr : H ↪g G ⊕g H).toHom

/-- 서로소 타입 합 위의 그래프는 연결 성분 수가 더해진다. -/
theorem card_connectedComponent_sum [Finite V] [Finite W] :
    Nat.card (G ⊕g H).ConnectedComponent =
      Nat.card G.ConnectedComponent + Nat.card H.ConnectedComponent := by
  let f : G.ConnectedComponent → (G ⊕g H).ConnectedComponent :=
    ConnectedComponent.map (Embedding.sumInl : G ↪g G ⊕g H).toHom
  let g : H.ConnectedComponent → (G ⊕g H).ConnectedComponent :=
    ConnectedComponent.map (Embedding.sumInr : H ↪g G ⊕g H).toHom
  let F := Sum.elim f g
  have hF : Function.Bijective F := by
    constructor
    · rintro (a | a) (b | b) h
      all_goals
        induction a using ConnectedComponent.ind with | h a => ?_
        induction b using ConnectedComponent.ind with | h b => ?_
      · have hr : (G ⊕g H).Reachable (.inl a) (.inl b) := ConnectedComponent.eq.mp h
        exact congrArg Sum.inl (ConnectedComponent.eq.mpr
          ((reachable_sum_inl_iff G H a b).mp hr))
      · have hr : (G ⊕g H).Reachable (.inl a) (.inr b) := ConnectedComponent.eq.mp h
        exact (not_reachable_sum_inl_inr a b hr).elim
      · have hr : (G ⊕g H).Reachable (.inr a) (.inl b) := ConnectedComponent.eq.mp h
        exact (not_reachable_sum_inl_inr b a hr.symm).elim
      · have hr : (G ⊕g H).Reachable (.inr a) (.inr b) := ConnectedComponent.eq.mp h
        exact congrArg Sum.inr (ConnectedComponent.eq.mpr
          ((reachable_sum_inr_iff G H a b).mp hr))
    · intro q
      induction q using ConnectedComponent.ind with
      | h x =>
        cases x with
        | inl a => exact ⟨.inl (G.connectedComponentMk a), rfl⟩
        | inr b => exact ⟨.inr (H.connectedComponentMk b), rfl⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_sum]

@[simp] theorem isIsolated_sum_inl (u : V) :
    (G ⊕g H).IsIsolated (.inl u) ↔ G.IsIsolated u := by
  simp [SimpleGraph.IsIsolated, Sum.forall]

@[simp] theorem isIsolated_sum_inr (u : W) :
    (G ⊕g H).IsIsolated (.inr u) ↔ H.IsIsolated u := by
  simp [SimpleGraph.IsIsolated, Sum.forall]

/-- 서로소 타입 합에서 고립점 수가 더해진다. -/
theorem ncard_isolated_sum [Finite V] [Finite W] :
    {u | (G ⊕g H).IsIsolated u}.ncard =
      {u | G.IsIsolated u}.ncard + {u | H.IsIsolated u}.ncard := by
  let e := (Equiv.subtypeSum (p := fun u ↦ (G ⊕g H).IsIsolated u)).trans
    (Equiv.sumCongr (Equiv.subtypeEquivRight (isIsolated_sum_inl G H))
      (Equiv.subtypeEquivRight (isIsolated_sum_inr G H)))
  change Nat.card {u // (G ⊕g H).IsIsolated u} =
    Nat.card {u // G.IsIsolated u} + Nat.card {u // H.IsIsolated u}
  rw [Nat.card_congr e, Nat.card_sum]

/-- 서로소 타입 합에서 변 수가 더해진다. -/
theorem ncard_edges_sum [Finite V] [Finite W] :
    (G ⊕g H).edgeSet.ncard = G.edgeSet.ncard + H.edgeSet.ncard := by
  change Nat.card (G ⊕g H).edgeSet = Nat.card G.edgeSet + Nat.card H.edgeSet
  rw [Nat.card_congr (SimpleGraph.edgeSetSumEquiv (G := G) (H := H)), Nat.card_sum]

namespace RotationSystem

/-- 서로소 타입 합에서 오일러 지표가 더해진다. -/
theorem sum_eulerChar [Finite V] [Finite W] (R : RotationSystem G) (S : RotationSystem H) :
    (R.sum G H S).eulerChar = R.eulerChar + S.eulerChar := by
  unfold eulerChar numFaces
  rw [Nat.card_sum, ncard_edges_sum, orbitCount_sum_facePerm, ncard_isolated_sum]
  simp only [Nat.cast_add]
  omega

end RotationSystem

/-- 서로소 타입 합 위의 두 평면 그래프를 합쳐도 평면이다. -/
theorem IsPlanar.sum [Finite V] [Finite W] (hG : IsPlanar G) (hH : IsPlanar H) :
    IsPlanar (G ⊕g H) := by
  obtain ⟨R, hR⟩ := hG
  obtain ⟨S, hS⟩ := hH
  refine ⟨R.sum G H S, ?_⟩
  rw [RotationSystem.sum_eulerChar, hR, hS, card_connectedComponent_sum]
  simp only [Nat.cast_add]
  omega

/-- 블루프린트 `lem:sum0`: 지지 집합이 서로소인 두 평면 그래프의 합집합은 평면이다. -/
theorem IsPlanar.sup_of_disjoint {V : Type*} [Finite V] {G₁ G₂ : SimpleGraph V}
    (hG₁ : IsPlanar G₁) (hG₂ : IsPlanar G₂) (hd : Disjoint G₁.support G₂.support) :
    IsPlanar (G₁ ⊔ G₂) := by
  classical
  let K₁ := G₁.induce G₁.support
  let K₂ := G₂.induce G₂.support
  have hK₁ : IsPlanar K₁ := (isPlanar_map_iff K₁ (Function.Embedding.subtype _)).mp (by
    change IsPlanar (G₁.induce G₁.support).spanningCoe
    simpa only [spanningCoe_induce_support] using hG₁)
  have hK₂ : IsPlanar K₂ := (isPlanar_map_iff K₂ (Function.Embedding.subtype _)).mp (by
    change IsPlanar (G₂.induce G₂.support).spanningCoe
    simpa only [spanningCoe_induce_support] using hG₂)
  let f : G₁.support ⊕ G₂.support ↪ V :=
    ⟨Sum.elim Subtype.val Subtype.val, by
      rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (Subtype.ext h)
      · change (a : V) = (b : V) at h
        exact (Set.disjoint_left.mp hd (h ▸ a.2) b.2).elim
      · change (a : V) = (b : V) at h
        exact (Set.disjoint_left.mp hd b.2 (h ▸ a.2)).elim
      · exact congrArg Sum.inr (Subtype.ext h)⟩
  have hP := (isPlanar_map_iff (K₁ ⊕g K₂) f).mpr (hK₁.sum _ _ hK₂)
  apply hP.mono
  intro a b hab
  apply (SimpleGraph.map_adj f _ a b).mpr
  rcases hab with hab | hab
  · exact ⟨.inl ⟨a, hab.mem_support_left⟩, .inl ⟨b, hab.mem_support_right⟩, hab, rfl, rfl⟩
  · exact ⟨.inr ⟨a, hab.mem_support_left⟩, .inr ⟨b, hab.mem_support_right⟩, hab, rfl, rfl⟩

end Kuratowski
