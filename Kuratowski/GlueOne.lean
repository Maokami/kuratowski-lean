import Kuratowski.Sum

/-!
# 한 점에서 평면 그래프 붙이기

변이 서로소인 두 그래프의 다트를 합치고, 공통 꼭짓점의 두 회전 순환을 호환으로 잇는다.
-/

namespace Kuratowski

open SimpleGraph Equiv Equiv.Perm

variable {V : Type*} {G H : SimpleGraph V}

/-- 공유하는 지지 집합이 한 점 이하면 공유하는 변은 없다. -/
theorem disjoint_of_support_inter_subsingleton (hs : (G.support ∩ H.support).Subsingleton) :
    Disjoint G H := by
  refine disjoint_iff_inf_le.mpr ?_
  intro u v huv
  exact (huv.1.ne (hs ⟨huv.1.mem_support_left, huv.2.mem_support_left⟩
    ⟨huv.1.mem_support_right, huv.2.mem_support_right⟩)).elim

/-- 변이 서로소인 그래프의 합집합 다트는 두 다트 집합의 서로소 합이다. -/
noncomputable def dartEquivSup (hd : Disjoint G H) : G.Dart ⊕ H.Dart ≃ (G ⊔ H).Dart := by
  classical
  exact
    { toFun := fun
        | .inl d => ⟨d.toProd, Or.inl d.adj⟩
        | .inr d => ⟨d.toProd, Or.inr d.adj⟩
      invFun := fun d ↦ if h : G.Adj d.fst d.snd then .inl ⟨d.toProd, h⟩
        else .inr ⟨d.toProd, d.adj.resolve_left h⟩
      left_inv := by
        rintro (d | d)
        · simp only [d.adj, ↓reduceDIte]
        · have hn : ¬ G.Adj d.fst d.snd := by
            intro hg
            exact (show (⊥ : SimpleGraph V).Adj d.fst d.snd from
              (disjoint_iff_inf_le.mp hd) ⟨hg, d.adj⟩).elim
          simp only [hn, ↓reduceDIte]
      right_inv := by
        intro d
        dsimp only
        split_ifs <;> rfl }

@[simp] theorem dartEquivSup_fst (hd : Disjoint G H) (d : G.Dart ⊕ H.Dart) :
    (dartEquivSup hd d).fst = Sum.elim (fun a : G.Dart ↦ a.fst) (fun b : H.Dart ↦ b.fst) d := by
  cases d <;> rfl

@[simp] theorem dartEquivSup_symm (hd : Disjoint G H) (d : G.Dart ⊕ H.Dart) :
    dartEquivSup hd (Sum.map Dart.symm Dart.symm d) = (dartEquivSup hd d).symm := by
  cases d <;> rfl

/-- 서로소 합 순열 안의 왼쪽 순환을 보존한다. -/
private theorem sameCycle_sumCongr_left {α β : Type*} [Finite α] [Finite β]
    (f : Perm α) (g : Perm β) {a b : α} (h : f.SameCycle a b) :
    (Perm.sumCongr f g).SameCycle (.inl a) (.inl b) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hp : ∀ n, ((Perm.sumCongr f g) ^ n) (.inl a) = .inl ((f ^ n) a) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ', Perm.mul_apply, ih, Perm.sumCongr_apply, Sum.map_inl]
  exact ⟨n, by simpa only [zpow_natCast, hp] using congrArg Sum.inl hn⟩

/-- 서로소 합 순열 안의 오른쪽 순환을 보존한다. -/
private theorem sameCycle_sumCongr_right {α β : Type*} [Finite α] [Finite β]
    (f : Perm α) (g : Perm β) {a b : β} (h : g.SameCycle a b) :
    (Perm.sumCongr f g).SameCycle (.inr a) (.inr b) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hp : ∀ n, ((Perm.sumCongr f g) ^ n) (.inr a) = .inr ((g ^ n) a) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ', Perm.mul_apply, ih, Perm.sumCongr_apply, Sum.map_inr]
  exact ⟨n, by simpa only [zpow_natCast, hp] using congrArg Sum.inr hn⟩

private theorem not_sameCycle_sumCongr_cross {α β : Type*} [Finite α] [Finite β]
    (f : Perm α) (g : Perm β) (a : α) (b : β) :
    ¬ (Perm.sumCongr f g).SameCycle (.inl a) (.inr b) := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hp : ∀ n, ((Perm.sumCongr f g) ^ n) (.inl a) = .inl ((f ^ n) a) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ', Perm.mul_apply, ih, Perm.sumCongr_apply, Sum.map_inl]
  rw [hp] at hn
  cases hn

namespace RotationSystem

/-- 두 그래프의 유일한 공통 꼭짓점에서 회전 순환들을 호환으로 잇는다. -/
noncomputable def glue [Finite V] (hd : Disjoint G H) (R : RotationSystem G)
    (S : RotationSystem H) (p : G.Dart) (q : H.Dart) (hpq : p.fst = q.fst)
    (hshare : ∀ (a : G.Dart) (b : H.Dart), a.fst = b.fst → a.fst = p.fst) :
    RotationSystem (G ⊔ H) := by
  classical
  let e := dartEquivSup hd
  let b := e.permCongr (Perm.sumCongr R.rot S.rot)
  let p₀ := e (.inl p)
  let q₀ := e (.inr q)
  have hfst : ∀ d, (b d).fst = d.fst := by
    intro d
    obtain ⟨d, rfl⟩ := e.surjective d
    simp only [b, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    cases d with
    | inl d => exact R.fst_rot d
    | inr d => exact S.fst_rot d
  have hleft : ∀ {a a' : G.Dart}, R.rot.SameCycle a a' → b.SameCycle (e (.inl a)) (e (.inl a')) :=
    fun h ↦ (sameCycle_permCongr_iff e _ _ _).mpr (sameCycle_sumCongr_left R.rot S.rot h)
  have hright : ∀ {a a' : H.Dart}, S.rot.SameCycle a a' → b.SameCycle (e (.inr a)) (e (.inr a')) :=
    fun h ↦ (sameCycle_permCongr_iff e _ _ _).mpr (sameCycle_sumCongr_right R.rot S.rot h)
  have hno : ¬ b.SameCycle p₀ q₀ := by
    intro h
    exact not_sameCycle_sumCongr_cross R.rot S.rot p q
      ((sameCycle_permCongr_iff e _ _ _).mp h)
  have hjoin : (b * swap p₀ q₀).SameCycle p₀ q₀ := sameCycle_mul_swap_of_not hno
  have hkeep : ∀ {a a'}, b.SameCycle a a' → (b * swap p₀ q₀).SameCycle a a' :=
    fun h ↦ hjoin.mul_swap_of_sameCycle h
  have hcross : ∀ (a : G.Dart) (a' : H.Dart), a.fst = a'.fst →
      (b * swap p₀ q₀).SameCycle (e (.inl a)) (e (.inr a')) := by
    intro a a' ha
    have hL := hkeep (hleft (R.sameCycle_rot a p (hshare a a' ha)))
    have hR := hkeep (hright (S.sameCycle_rot a' q (ha.symm.trans ((hshare a a' ha).trans hpq))))
    exact hL.trans (hjoin.trans hR.symm)
  refine { rot := b * swap p₀ q₀, fst_rot := ?_, sameCycle_rot := ?_ }
  · intro d
    rw [Perm.mul_apply, hfst]
    by_cases hp : d = p₀
    · subst d
      rw [swap_apply_left]
      exact hpq.symm
    by_cases hq : d = q₀
    · subst d
      rw [swap_apply_right]
      exact hpq
    rw [swap_apply_of_ne_of_ne hp hq]
  · intro d d' hd'
    obtain ⟨d, rfl⟩ := e.surjective d
    obtain ⟨d', rfl⟩ := e.surjective d'
    rcases d with d | d <;> rcases d' with d' | d'
    · exact hkeep (hleft (R.sameCycle_rot d d' hd'))
    · exact hcross d d' hd'
    · exact (hcross d' d hd'.symm).symm
    · exact hkeep (hright (S.sameCycle_rot d d' hd'))

/-- 공통 꼭짓점의 두 회전을 이으면 두 면 순환이 하나로 합쳐진다. -/
theorem orbitCount_glue_facePerm [Finite V] (hd : Disjoint G H) (R : RotationSystem G)
    (S : RotationSystem H) (p : G.Dart) (q : H.Dart) (hpq : p.fst = q.fst)
    (hshare : ∀ (a : G.Dart) (b : H.Dart), a.fst = b.fst → a.fst = p.fst) :
    orbitCount (glue hd R S p q hpq hshare).facePerm + 1 =
      orbitCount R.facePerm + orbitCount S.facePerm := by
  classical
  let e := dartEquivSup hd
  let p₀ := e (.inl p)
  let q₀ := e (.inr q)
  have hsymm : ∀ d, e.symm d.symm = Sum.map Dart.symm Dart.symm (e.symm d) := by
    intro d
    apply e.injective
    simp only [e, dartEquivSup_symm, Equiv.apply_symm_apply]
  have hbase : ∀ d, (e.permCongr (Perm.sumCongr R.rot S.rot)) d.symm =
      (e.permCongr (Perm.sumCongr R.facePerm S.facePerm)) d := by
    intro d
    simp only [Equiv.permCongr_apply, hsymm]
    cases e.symm d <;> rfl
  have hface : (glue hd R S p q hpq hshare).facePerm =
      e.permCongr (Perm.sumCongr R.facePerm S.facePerm) * swap p₀.symm q₀.symm := by
    ext1 d
    change (e.permCongr (Perm.sumCongr R.rot S.rot)) (swap p₀ q₀ d.symm) = _
    have hs := Dart.symm_involutive.injective.map_swap p₀.symm q₀.symm d
    simp only [Dart.symm_symm] at hs
    rw [← hs, hbase]
    rfl
  have hn : ¬ (e.permCongr (Perm.sumCongr R.facePerm S.facePerm)).SameCycle p₀.symm q₀.symm := by
    intro h
    have hp : p₀.symm = e (.inl p.symm) := rfl
    have hq : q₀.symm = e (.inr q.symm) := rfl
    rw [hp, hq] at h
    exact not_sameCycle_sumCongr_cross R.facePerm S.facePerm p.symm q.symm
      ((sameCycle_permCongr_iff e _ _ _).mp h)
  rw [hface]
  have hc := orbitCount_mul_swap_of_not_sameCycle hn
  rw [orbitCount_permCongr, orbitCount_sumCongr] at hc
  exact hc

end RotationSystem

/-! ### 한 점 합집합의 연결 성분 -/

private abbrev SupportComponent (G : SimpleGraph V) :=
  (G.induce G.support).ConnectedComponent

private abbrev GlueIndex (v : V) (hvH : v ∈ H.support) :=
  SupportComponent G ⊕
    ({c : SupportComponent H // c ≠ (H.induce H.support).connectedComponentMk ⟨v, hvH⟩} ⊕
      {u : V // u ∉ G.support ∧ u ∉ H.support})

private noncomputable def componentLabel (v : V) (hvG : v ∈ G.support) (hvH : v ∈ H.support)
    (u : V) : GlueIndex (G := G) v hvH := by
  classical
  exact if huG : u ∈ G.support then
    .inl ((G.induce G.support).connectedComponentMk ⟨u, huG⟩)
  else if huH : u ∈ H.support then
    if hc : (H.induce H.support).connectedComponentMk ⟨u, huH⟩ =
        (H.induce H.support).connectedComponentMk ⟨v, hvH⟩ then
      .inl ((G.induce G.support).connectedComponentMk ⟨v, hvG⟩)
    else .inr (.inl ⟨(H.induce H.support).connectedComponentMk ⟨u, huH⟩, hc⟩)
  else .inr (.inr ⟨u, huG, huH⟩)

private theorem componentLabel_of_G (v : V) (hvG : v ∈ G.support) (hvH : v ∈ H.support)
    {u : V} (huG : u ∈ G.support) : componentLabel v hvG hvH u =
      .inl ((G.induce G.support).connectedComponentMk ⟨u, huG⟩) := by
  classical
  simp only [componentLabel, huG, ↓reduceDIte]

private noncomputable def componentLabelH (v : V) (hvG : v ∈ G.support) (hvH : v ∈ H.support)
    (u : V) (huH : u ∈ H.support) : GlueIndex (G := G) v hvH := by
  classical
  exact if hc : (H.induce H.support).connectedComponentMk ⟨u, huH⟩ =
      (H.induce H.support).connectedComponentMk ⟨v, hvH⟩ then
    .inl ((G.induce G.support).connectedComponentMk ⟨v, hvG⟩)
  else .inr (.inl ⟨(H.induce H.support).connectedComponentMk ⟨u, huH⟩, hc⟩)

private theorem componentLabel_of_H (v : V) (hvG : v ∈ G.support) (hvH : v ∈ H.support)
    (hs : ∀ u, u ∈ G.support → u ∈ H.support → u = v) {u : V} (huH : u ∈ H.support) :
    componentLabel v hvG hvH u = componentLabelH v hvG hvH u huH := by
  classical
  by_cases huG : u ∈ G.support
  · have he := hs u huG huH
    subst u
    simp [componentLabel, componentLabelH, hvG]
  · simp only [componentLabel, componentLabelH, huG, huH, ↓reduceDIte]

private theorem componentLabel_adj (v : V) (hvG : v ∈ G.support) (hvH : v ∈ H.support)
    (hs : ∀ u, u ∈ G.support → u ∈ H.support → u = v) {u w : V} (h : (G ⊔ H).Adj u w) :
    componentLabel v hvG hvH u = componentLabel v hvG hvH w := by
  classical
  rcases h with h | h
  · rw [componentLabel_of_G v hvG hvH h.mem_support_left,
      componentLabel_of_G v hvG hvH h.mem_support_right]
    exact congrArg Sum.inl (ConnectedComponent.eq.mpr
      (show (G.induce G.support).Adj
        ⟨u, h.mem_support_left⟩ ⟨w, h.mem_support_right⟩ from h).reachable)
  · rw [componentLabel_of_H v hvG hvH hs h.mem_support_left,
      componentLabel_of_H v hvG hvH hs h.mem_support_right]
    have hc : (H.induce H.support).connectedComponentMk ⟨u, h.mem_support_left⟩ =
        (H.induce H.support).connectedComponentMk ⟨w, h.mem_support_right⟩ :=
      ConnectedComponent.eq.mpr
        (show (H.induce H.support).Adj
          ⟨u, h.mem_support_left⟩ ⟨w, h.mem_support_right⟩ from h).reachable
    unfold componentLabelH
    rw [hc]

private def supportHomLeft : G.induce G.support →g G ⊔ H where
  toFun := Subtype.val
  map_rel' h := Or.inl h

private def supportHomRight : H.induce H.support →g G ⊔ H where
  toFun := Subtype.val
  map_rel' h := Or.inr h

private theorem componentLabel_walk (v : V) (hvG : v ∈ G.support) (hvH : v ∈ H.support)
    (hs : ∀ u, u ∈ G.support → u ∈ H.support → u = v) {u w : V} (p : (G ⊔ H).Walk u w) :
    componentLabel v hvG hvH u = componentLabel v hvG hvH w := by
  induction p with
  | nil => rfl
  | cons h p ih => exact (componentLabel_adj v hvG hvH hs h).trans ih

private noncomputable def classifyComponent (v : V) (hvG : v ∈ G.support) (hvH : v ∈ H.support)
    (hs : ∀ u, u ∈ G.support → u ∈ H.support → u = v) :
    (G ⊔ H).ConnectedComponent → GlueIndex (G := G) v hvH :=
  ConnectedComponent.lift (componentLabel v hvG hvH)
    (fun _ _ p _ ↦ componentLabel_walk v hvG hvH hs p)

private def unlabelComponent (v : V) (hvH : v ∈ H.support) :
    GlueIndex (G := G) v hvH → (G ⊔ H).ConnectedComponent
  | .inl c => c.map (supportHomLeft (G := G) (H := H))
  | .inr (.inl c) => c.val.map (supportHomRight (G := G) (H := H))
  | .inr (.inr u) => (G ⊔ H).connectedComponentMk u.val

private theorem classify_unlabel (v : V) (hvG : v ∈ G.support) (hvH : v ∈ H.support)
    (hs : ∀ u, u ∈ G.support → u ∈ H.support → u = v) :
    Function.LeftInverse (classifyComponent v hvG hvH hs) (unlabelComponent (G := G) v hvH) := by
  classical
  rintro (c | c | u)
  · induction c using ConnectedComponent.ind with
    | h u => exact componentLabel_of_G v hvG hvH u.property
  · rcases c with ⟨c, hc⟩
    induction c using ConnectedComponent.ind with
    | h u =>
      change componentLabel v hvG hvH u.val = _
      rw [componentLabel_of_H v hvG hvH hs u.property]
      simp only [componentLabelH, hc, ↓reduceDIte]
  · change componentLabel v hvG hvH u.val = _
    simp only [componentLabel, u.property.1, u.property.2, ↓reduceDIte]

private theorem unlabel_classify (v : V) (hvG : v ∈ G.support) (hvH : v ∈ H.support)
    (hs : ∀ u, u ∈ G.support → u ∈ H.support → u = v) :
    Function.RightInverse (classifyComponent v hvG hvH hs) (unlabelComponent (G := G) v hvH) := by
  classical
  intro c
  induction c using ConnectedComponent.ind with
  | h u =>
    change unlabelComponent v hvH (componentLabel v hvG hvH u) = (G ⊔ H).connectedComponentMk u
    by_cases huG : u ∈ G.support
    · simp only [componentLabel, huG, ↓reduceDIte]
      rfl
    by_cases huH : u ∈ H.support
    · simp only [componentLabel, huG, huH, ↓reduceDIte]
      split_ifs with hc
      · have he := congrArg (ConnectedComponent.map (supportHomRight (G := G) (H := H))) hc
        exact he.symm
      · rfl
    · simp only [componentLabel, huG, huH, ↓reduceDIte]
      rfl

/-- 한 점에서 만나는 그래프의 연결 성분 수를 고정된 꼭짓점 타입에서 센다. -/
theorem card_connectedComponent_sup_of_inter_eq_singleton [Finite V] {v : V}
    (hs : G.support ∩ H.support = {v}) :
    Nat.card (G ⊔ H).ConnectedComponent + Nat.card V =
      Nat.card G.ConnectedComponent + Nat.card H.ConnectedComponent := by
  classical
  have hv : v ∈ G.support ∩ H.support := by rw [hs]; exact Set.mem_singleton v
  have hshare : ∀ u, u ∈ G.support → u ∈ H.support → u = v := by
    intro u huG huH
    have hu : u ∈ G.support ∩ H.support := ⟨huG, huH⟩
    rwa [hs, Set.mem_singleton_iff] at hu
  let e : GlueIndex (G := G) v hv.2 ≃ (G ⊔ H).ConnectedComponent :=
    ⟨unlabelComponent v hv.2, classifyComponent v hv.1 hv.2 hshare,
      classify_unlabel v hv.1 hv.2 hshare, unlabel_classify v hv.1 hv.2 hshare⟩
  have hC := Nat.card_congr e
  dsimp only [GlueIndex] at hC
  rw [Nat.card_sum, Nat.card_sum] at hC
  change Nat.card (SupportComponent G) +
    (Nat.card {c : SupportComponent H // c ≠ (H.induce H.support).connectedComponentMk ⟨v, hv.2⟩} +
      Nat.card {u : V // u ∉ G.support ∧ u ∉ H.support}) =
      Nat.card (G ⊔ H).ConnectedComponent at hC
  have hG := card_connectedComponent_map_add (G.induce G.support) (Function.Embedding.subtype _)
  have hH := card_connectedComponent_map_add (H.induce H.support) (Function.Embedding.subtype _)
  change Nat.card (G.induce G.support).spanningCoe.ConnectedComponent + Nat.card G.support =
    Nat.card (SupportComponent G) + Nat.card V at hG
  change Nat.card (H.induce H.support).spanningCoe.ConnectedComponent + Nat.card H.support =
    Nat.card (SupportComponent H) + Nat.card V at hH
  rw [spanningCoe_induce_support] at hG hH
  rw [Nat.card_coe_set_eq] at hG hH
  have hB := Set.ncard_add_ncard_compl
    ({(H.induce H.support).connectedComponentMk ⟨v, hv.2⟩} : Set (SupportComponent H))
  rw [Set.ncard_singleton] at hB
  change 1 + Nat.card {c : SupportComponent H //
      c ≠ (H.induce H.support).connectedComponentMk ⟨v, hv.2⟩} = Nat.card (SupportComponent H) at hB
  have hU := Set.ncard_union_add_ncard_inter G.support H.support
  rw [hs, Set.ncard_singleton] at hU
  have hN := Set.ncard_add_ncard_compl (G.support ∪ H.support)
  have heq : (G.support ∪ H.support)ᶜ = {u | u ∉ G.support ∧ u ∉ H.support} := by
    ext u
    simp
  rw [heq] at hN
  change (G.support ∪ H.support).ncard + Nat.card {u // u ∉ G.support ∧ u ∉ H.support} =
    Nat.card V at hN
  omega

/-- 한 점에서 만나는 그래프의 고립점 수를 고정된 꼭짓점 타입에서 센다. -/
theorem ncard_isolated_sup_of_inter_eq_singleton [Finite V] {v : V}
    (hs : G.support ∩ H.support = {v}) :
    {u | (G ⊔ H).IsIsolated u}.ncard + Nat.card V =
      {u | G.IsIsolated u}.ncard + {u | H.IsIsolated u}.ncard + 1 := by
  have hsup : (G ⊔ H).support = G.support ∪ H.support := by
    ext u
    simp [SimpleGraph.mem_support, exists_or]
  have hc (K : SimpleGraph V) : K.supportᶜ = {u | K.IsIsolated u} := by
    ext u
    simp
  have hG := Set.ncard_add_ncard_compl G.support
  have hH := Set.ncard_add_ncard_compl H.support
  have hU := Set.ncard_add_ncard_compl (G ⊔ H).support
  rw [hc] at hG hH hU
  rw [hsup] at hU
  have hI := Set.ncard_union_add_ncard_inter G.support H.support
  rw [hs, Set.ncard_singleton] at hI
  omega

/-- 블루프린트 `lem:sum1`: 지지 집합이 꼭짓점 하나에서 만나는 평면 그래프의 합집합은 평면이다. -/
theorem IsPlanar.sup_of_inter_eq_singleton [Finite V] {v : V} (hG : IsPlanar G) (hH : IsPlanar H)
    (hs : G.support ∩ H.support = {v}) : IsPlanar (G ⊔ H) := by
  classical
  obtain ⟨R, hR⟩ := hG
  obtain ⟨S, hS⟩ := hH
  have hv : v ∈ G.support ∩ H.support := by rw [hs]; exact Set.mem_singleton v
  have hd : Disjoint G H := disjoint_of_support_inter_subsingleton (by
    rw [hs]
    exact Set.subsingleton_singleton)
  obtain ⟨u, hu⟩ := G.mem_support.mp hv.1
  obtain ⟨w, hw⟩ := H.mem_support.mp hv.2
  let p : G.Dart := ⟨(v, u), hu⟩
  let q : H.Dart := ⟨(v, w), hw⟩
  have hshare : ∀ (a : G.Dart) (b : H.Dart), a.fst = b.fst → a.fst = p.fst := by
    intro a b hab
    have ha : a.fst ∈ G.support ∩ H.support :=
      ⟨a.adj.mem_support_left, by rw [hab]; exact b.adj.mem_support_left⟩
    change a.fst = v
    rwa [hs, Set.mem_singleton_iff] at ha
  let T := RotationSystem.glue hd R S p q rfl hshare
  refine ⟨T, ?_⟩
  have hO := RotationSystem.orbitCount_glue_facePerm hd R S p q rfl hshare
  have hE : (G ⊔ H).edgeSet.ncard = G.edgeSet.ncard + H.edgeSet.ncard := by
    rw [edgeSet_sup, Set.ncard_union_eq (SimpleGraph.disjoint_edgeSet.mpr hd)]
  have hI := ncard_isolated_sup_of_inter_eq_singleton hs
  have hC := card_connectedComponent_sup_of_inter_eq_singleton hs
  have hO' := congrArg (fun n : ℕ ↦ (n : ℤ)) hO
  have hE' := congrArg (fun n : ℕ ↦ (n : ℤ)) hE
  have hI' := congrArg (fun n : ℕ ↦ (n : ℤ)) hI
  have hC' := congrArg (fun n : ℕ ↦ (n : ℤ)) hC
  unfold RotationSystem.eulerChar RotationSystem.numFaces at hR hS ⊢
  push_cast at hR hS hO' hE' hI' hC' ⊢
  change orbitCount T.facePerm + 1 = _ at hO
  change (orbitCount T.facePerm : ℤ) + 1 = _ at hO'
  omega

end Kuratowski
