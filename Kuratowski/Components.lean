import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# 연결 성분, 변, 고립점의 개수

변 하나를 지우거나 세분하거나, 꼭짓점 단사로 그래프를 옮길 때
연결 성분의 수, 변의 수, 고립점의 수가 어떻게 바뀌는지 정리한다.
-/

namespace Kuratowski
open SimpleGraph

variable {V : Type*} [Finite V]

/-- 변 `xy`를 새 꼭짓점 `w`로 세분한다: `xy`를 지우고 `xw`, `wy`를 넣는다. -/
def subdivideEdge (H : SimpleGraph V) (x y w : V) : SimpleGraph V :=
  H.deleteEdges {s(x, y)} ⊔ edge x w ⊔ edge w y

omit [Finite V] in
theorem subdivideEdge_adj {H : SimpleGraph V} {x y w : V} (hxw : x ≠ w) (hwy : w ≠ y) {p q : V} :
    (subdivideEdge H x y w).Adj p q ↔
      (H.Adj p q ∧ s(p, q) ≠ s(x, y)) ∨ s(p, q) = s(x, w) ∨ s(p, q) = s(w, y) := by
  simp only [subdivideEdge, sup_adj, deleteEdges_adj, Set.mem_singleton_iff, edge_adj,
    Sym2.eq_iff, ne_eq]
  constructor
  · tauto
  · rintro (h | (h | h) | (h | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨Or.inl h, by rw [h.1, h.2]; exact hxw⟩)
    · exact Or.inl (Or.inr ⟨Or.inr h, by rw [h.1, h.2]; exact hxw.symm⟩)
    · exact Or.inr ⟨Or.inl h, by rw [h.1, h.2]; exact hwy⟩
    · exact Or.inr ⟨Or.inr h, by rw [h.1, h.2]; exact hwy.symm⟩

/-! ### 보조정리 -/

omit [Finite V] in
/-- 인접한 두 점이 `G'`에서 (`f`로 옮긴 뒤) 이어져 있으면, `G`에서 이어진 두 점도 그렇다. -/
theorem reachable_of_forall_adj {G G' : SimpleGraph V} (f : V → V)
    (hf : ∀ a b, G.Adj a b → G'.Reachable (f a) (f b)) {a b : V} (h : G.Reachable a b) :
    G'.Reachable (f a) (f b) := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hcb ih => exact ih.trans (hf _ _ hcb)

omit [Finite V] in
/-- 고립점에서 갈 수 있는 점은 자기 자신뿐이다. -/
theorem eq_of_isIsolated_of_reachable {G : SimpleGraph V} {a b : V} (ha : G.IsIsolated a)
    (h : G.Reachable a b) : b = a := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hcb ih =>
    subst ih
    exact (ha _ hcb).elim

omit [Finite V] in
/-- `G`의 변 가운데 `uv`가 아닌 것이 모두 `G'`의 변이면, `G`에서 이어진 두 점은
`G'`에서 이어져 있거나, 둘 다 `G'`에서 `u` 또는 `v`에 이어져 있다. -/
theorem reachable_or_of_adj_of_ne {G G' : SimpleGraph V} {u v : V}
    (hadj : ∀ a b, G.Adj a b → s(a, b) ≠ s(u, v) → G'.Adj a b) {a b : V} (h : G.Reachable a b) :
    G'.Reachable a b ∨
      ((G'.Reachable a u ∨ G'.Reachable a v) ∧ (G'.Reachable b u ∨ G'.Reachable b v)) := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl Reachable.rfl
  | @tail c b _ hcb ih =>
    have hstep : G'.Reachable c b ∨
        ((G'.Reachable c u ∨ G'.Reachable c v) ∧ (G'.Reachable b u ∨ G'.Reachable b v)) := by
      by_cases he : s(c, b) = s(u, v)
      · right
        rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨Or.inl (by rw [h1]), Or.inr (by rw [h2])⟩
        · exact ⟨Or.inr (by rw [h1]), Or.inl (by rw [h2])⟩
      · exact Or.inl (hadj c b hcb he).reachable
    rcases ih with hac | ⟨ha, hc⟩ <;> rcases hstep with hcb' | ⟨hc', hb⟩
    · exact Or.inl (hac.trans hcb')
    · exact Or.inr ⟨hc'.imp hac.trans hac.trans, hb⟩
    · exact Or.inr ⟨ha, hc.imp hcb'.symm.trans hcb'.symm.trans⟩
    · exact Or.inr ⟨ha, hb⟩

omit [Finite V] in
theorem adj_deleteEdges_of_ne {G : SimpleGraph V} {u v : V} :
    ∀ a b, G.Adj a b → s(a, b) ≠ s(u, v) → (G.deleteEdges {s(u, v)}).Adj a b :=
  fun _ _ hab he => (deleteEdges_adj ..).mpr ⟨hab, he⟩

/-! ### 변 하나 지우기 -/

-- 변 하나를 지우면 연결 성분은 많아야 하나 는다.
theorem card_connectedComponent_deleteEdges_le (G : SimpleGraph V) (u v : V) :
    Nat.card (G.deleteEdges {s(u, v)}).ConnectedComponent ≤ Nat.card G.ConnectedComponent + 1 := by
  classical
  have hle : G.deleteEdges {s(u, v)} ≤ G := deleteEdges_le _
  let f : (G.deleteEdges {s(u, v)}).ConnectedComponent → Option G.ConnectedComponent :=
    fun C => if C = (G.deleteEdges {s(u, v)}).connectedComponentMk v then none
      else some (C.map (Hom.ofLE hle))
  have hf : Function.Injective f := by
    intro C₁ C₂
    refine ConnectedComponent.ind₂ (fun a b => ?_) C₁ C₂
    intro h
    simp only [f, ConnectedComponent.map_mk, Hom.ofLE_apply] at h
    split_ifs at h with ha hb hb
    · rw [ha, hb]
    · rw [ConnectedComponent.eq] at ha hb
      rw [ConnectedComponent.eq]
      have hab := ConnectedComponent.exact (Option.some.inj h)
      rcases reachable_or_of_adj_of_ne adj_deleteEdges_of_ne hab with h' | ⟨ha', hb'⟩
      · exact h'
      · exact (ha'.resolve_right ha).trans (hb'.resolve_right hb).symm
  calc Nat.card (G.deleteEdges {s(u, v)}).ConnectedComponent
      ≤ Nat.card (Option G.ConnectedComponent) := Nat.card_le_card_of_injective f hf
    _ = Nat.card G.ConnectedComponent + 1 := Finite.card_option

omit [Finite V] in
-- 지운 변의 두 끝이 여전히 이어져 있으면 연결 성분 수는 그대로다.
theorem card_connectedComponent_deleteEdges_eq (G : SimpleGraph V) {u v : V}
    (h : (G.deleteEdges {s(u, v)}).Reachable u v) :
    Nat.card (G.deleteEdges {s(u, v)}).ConnectedComponent = Nat.card G.ConnectedComponent := by
  have key : ∀ a b, (G.deleteEdges {s(u, v)}).Reachable a b ↔ G.Reachable a b := by
    intro a b
    refine ⟨fun hab => hab.mono (deleteEdges_le _), fun hab => ?_⟩
    rcases reachable_or_of_adj_of_ne adj_deleteEdges_of_ne hab with h' | ⟨ha, hb⟩
    · exact h'
    · have ha' := ha.elim id (fun hav => hav.trans h.symm)
      have hb' := hb.elim id (fun hbv => hbv.trans h.symm)
      exact ha'.trans hb'.symm
  exact Nat.card_congr (Quot.congr (Equiv.refl V) key)

theorem ncard_edgeSet_deleteEdges (G : SimpleGraph V) {u v : V} (h : G.Adj u v) :
    (G.deleteEdges {s(u, v)}).edgeSet.ncard + 1 = G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  exact Set.ncard_sdiff_singleton_add_one (G.mem_edgeSet.mpr h)

omit [Finite V] in
-- 변이 없는 그래프는 꼭짓점마다 성분 하나.
theorem card_connectedComponent_of_edgeSet_eq_empty (G : SimpleGraph V) (h : G.edgeSet = ∅) :
    Nat.card G.ConnectedComponent = Nat.card V := by
  rw [edgeSet_eq_empty] at h
  subst h
  refine (Nat.card_eq_of_bijective (⊥ : SimpleGraph V).connectedComponentMk ⟨?_, ?_⟩).symm
  · intro a b hab
    exact reachable_bot.mp (ConnectedComponent.exact hab)
  · intro C
    exact ConnectedComponent.ind (fun v => ⟨v, rfl⟩) C

-- 고립점은 각각 성분 하나이고, 변이 있으면 성분이 적어도 하나 더 있다.
theorem ncard_isolated_add_one_le (G : SimpleGraph V) {u v : V} (h : G.Adj u v) :
    {w | G.IsIsolated w}.ncard + 1 ≤ Nat.card G.ConnectedComponent := by
  let f : Option {w | G.IsIsolated w} → G.ConnectedComponent :=
    fun o => o.elim (G.connectedComponentMk u) (fun w => G.connectedComponentMk w)
  have hf : Function.Injective f := by
    rintro (_ | ⟨a, ha⟩) (_ | ⟨b, hb⟩) hab <;> simp only [f, Option.elim] at hab
    · rfl
    · have := eq_of_isIsolated_of_reachable hb (ConnectedComponent.exact hab).symm
      subst this
      exact (hb _ h).elim
    · have := eq_of_isIsolated_of_reachable ha (ConnectedComponent.exact hab)
      subst this
      exact (ha _ h).elim
    · have := eq_of_isIsolated_of_reachable ha (ConnectedComponent.exact hab)
      subst this
      rfl
  rw [← Nat.card_coe_set_eq, ← Finite.card_option]
  exact Nat.card_le_card_of_injective f hf

/-! ### 변 세분 -/

omit [Finite V] in
theorem ne_of_subdivide {H : SimpleGraph V} {x y w : V} (hxy : H.Adj x y) (hw : H.IsIsolated w) :
    x ≠ w ∧ w ≠ y :=
  ⟨fun h => hw y (h ▸ hxy), fun h => hw x (h ▸ hxy.symm)⟩

omit [Finite V] in
/-- `H`에서 이어진 두 점은 세분한 그래프에서도 이어져 있다. -/
theorem reachable_subdivideEdge_of_reachable {H : SimpleGraph V} {x y w : V}
    (hxy : H.Adj x y) (hw : H.IsIsolated w) {a b : V} (h : H.Reachable a b) :
    (subdivideEdge H x y w).Reachable a b := by
  obtain ⟨hxw, hwy⟩ := ne_of_subdivide hxy hw
  have hxwy : (subdivideEdge H x y w).Reachable x y :=
    (Adj.reachable ((subdivideEdge_adj hxw hwy).mpr (Or.inr (Or.inl rfl)))).trans
      (Adj.reachable ((subdivideEdge_adj hxw hwy).mpr (Or.inr (Or.inr rfl))))
  refine reachable_of_forall_adj id (fun p q hpq => ?_) h
  by_cases he : s(p, q) = s(x, y)
  · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [id, h1, h2]; exact hxwy
    · simp only [id, h1, h2]; exact hxwy.symm
  · exact ((subdivideEdge_adj hxw hwy).mpr (Or.inl ⟨hpq, he⟩)).reachable

omit [Finite V] in
/-- 세분한 그래프에서 이어진 두 점은, `w`를 `x`로 보내면 `H`에서 이어져 있다. -/
theorem reachable_collapse [DecidableEq V] {H : SimpleGraph V} {x y w : V}
    (hxy : H.Adj x y) (hw : H.IsIsolated w) {a b : V} (h : (subdivideEdge H x y w).Reachable a b) :
    H.Reachable (if a = w then x else a) (if b = w then x else b) := by
  obtain ⟨hxw, hwy⟩ := ne_of_subdivide hxy hw
  refine reachable_of_forall_adj (fun p => if p = w then x else p) (fun p q hpq => ?_) h
  rcases (subdivideEdge_adj hxw hwy).mp hpq with ⟨hpq, -⟩ | hpq | hpq
  · have hp : p ≠ w := fun hp => hw q (hp ▸ hpq)
    have hq : q ≠ w := fun hq => hw p (hq ▸ hpq.symm)
    simp only [hp, hq, ite_false]
    exact hpq.reachable
  · rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2, hxw]
  · rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1, h2, ite_true, hwy.symm, ite_false]; exact hxy.reachable
    · simp only [h1, h2, ite_true, hwy.symm, ite_false]; exact hxy.symm.reachable

-- 세분: `H`의 변 `xy`를 `H`의 고립점 `w`로 세분한 그래프 `H₂`에 대해
theorem card_connectedComponent_subdivideEdge {H : SimpleGraph V} {x y w : V}
    (hxy : H.Adj x y) (hw : H.IsIsolated w) :
    Nat.card H.ConnectedComponent = Nat.card (subdivideEdge H x y w).ConnectedComponent + 1 := by
  classical
  obtain ⟨hxw, hwy⟩ := ne_of_subdivide hxy hw
  have toC : ∀ p, (subdivideEdge H x y w).Reachable p (if p = w then x else p) := by
    intro p
    split_ifs with hp
    · rw [hp]
      exact ((subdivideEdge_adj hxw hwy).mpr (Or.inr (Or.inl Sym2.eq_swap))).reachable
    · rfl
  have hne : ∀ p, (if p = w then x else p) ≠ w := by
    intro p
    split_ifs with hp
    · exact hxw
    · exact hp
  let g : (subdivideEdge H x y w).ConnectedComponent → H.ConnectedComponent :=
    ConnectedComponent.lift (fun p => H.connectedComponentMk (if p = w then x else p))
      (fun _ _ q _ => ConnectedComponent.sound (reachable_collapse hxy hw q.reachable))
  let f : Option (subdivideEdge H x y w).ConnectedComponent → H.ConnectedComponent :=
    fun o => o.elim (H.connectedComponentMk w) g
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro (_ | C₁) (_ | C₂) h
      · rfl
      · induction C₂ using ConnectedComponent.ind with
        | h q =>
          simp only [f, g, Option.elim, ConnectedComponent.lift_mk] at h
          exact (hne q (eq_of_isIsolated_of_reachable hw (ConnectedComponent.exact h))).elim
      · induction C₁ using ConnectedComponent.ind with
        | h p =>
          simp only [f, g, Option.elim, ConnectedComponent.lift_mk] at h
          exact (hne p (eq_of_isIsolated_of_reachable hw (ConnectedComponent.exact h).symm)).elim
      · induction C₁ using ConnectedComponent.ind with
        | h p =>
        induction C₂ using ConnectedComponent.ind with
        | h q =>
          simp only [f, g, Option.elim, ConnectedComponent.lift_mk] at h
          have hpq := reachable_subdivideEdge_of_reachable hxy hw (ConnectedComponent.exact h)
          exact congrArg some (ConnectedComponent.sound ((toC p).trans (hpq.trans (toC q).symm)))
    · intro C
      induction C using ConnectedComponent.ind with
      | h v =>
        by_cases hv : v = w
        · exact ⟨none, by rw [hv]; rfl⟩
        · refine ⟨some ((subdivideEdge H x y w).connectedComponentMk v), ?_⟩
          simp only [f, g, Option.elim, ConnectedComponent.lift_mk, hv, ite_false]
  rw [← Finite.card_option]
  exact (Nat.card_eq_of_bijective f hf).symm

theorem ncard_edgeSet_subdivideEdge {H : SimpleGraph V} {x y w : V}
    (hxy : H.Adj x y) (hw : H.IsIsolated w) :
    (subdivideEdge H x y w).edgeSet.ncard = H.edgeSet.ncard + 1 := by
  obtain ⟨hxw, hwy⟩ := ne_of_subdivide hxy hw
  have hE : (subdivideEdge H x y w).edgeSet =
      insert s(x, w) (insert s(w, y) (H.edgeSet \ {s(x, y)})) := by
    ext e
    induction e with
    | h p q =>
      rw [mem_edgeSet, subdivideEdge_adj hxw hwy]
      simp only [Set.mem_insert_iff, Set.mem_sdiff, mem_edgeSet, Set.mem_singleton_iff]
      tauto
  have h1 : s(w, y) ∉ H.edgeSet \ {s(x, y)} := fun h => hw y h.1
  have h2 : s(x, w) ∉ insert s(w, y) (H.edgeSet \ {s(x, y)}) := by
    rintro (h | h)
    · rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
      · exact hxw h
      · exact hxy.ne h
    · exact hw x (H.mem_edgeSet.mp h.1).symm
  have h3 := Set.ncard_sdiff_singleton_add_one (H.mem_edgeSet.mpr hxy)
  rw [hE, Set.ncard_insert_of_notMem h2, Set.ncard_insert_of_notMem h1, ← h3]

theorem ncard_isolated_subdivideEdge {H : SimpleGraph V} {x y w : V}
    (hxy : H.Adj x y) (hw : H.IsIsolated w) :
    {v | H.IsIsolated v}.ncard = {v | (subdivideEdge H x y w).IsIsolated v}.ncard + 1 := by
  obtain ⟨hxw, hwy⟩ := ne_of_subdivide hxy hw
  have hS : {v | (subdivideEdge H x y w).IsIsolated v} = {v | H.IsIsolated v} \ {w} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · intro hv
      refine ⟨fun z hvz => ?_, fun hvw => ?_⟩
      · by_cases he : s(v, z) = s(x, y)
        · rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hv w ((subdivideEdge_adj hxw hwy).mpr (Or.inr (Or.inl (by rw [h1]))))
          · exact hv w ((subdivideEdge_adj hxw hwy).mpr
              (Or.inr (Or.inr (by rw [h1, Sym2.eq_swap]))))
        · exact hv z ((subdivideEdge_adj hxw hwy).mpr (Or.inl ⟨hvz, he⟩))
      · exact hv x ((subdivideEdge_adj hxw hwy).mpr
          (Or.inr (Or.inl (by rw [hvw, Sym2.eq_swap]))))
    · rintro ⟨hv, hvw⟩ z hvz
      rcases (subdivideEdge_adj hxw hwy).mp hvz with ⟨h, -⟩ | h | h
      · exact hv z h
      · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hv y (h1 ▸ hxy)
        · exact hvw h1
      · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hvw h1
        · exact hv x (h1 ▸ hxy.symm)
  rw [hS, Set.ncard_sdiff_singleton_add_one (show w ∈ {v | H.IsIsolated v} from hw)]

/-! ### 꼭짓점 단사로 옮기기 -/

-- 꼭짓점 단사 `f : W ↪ V`로 옮긴 그래프 (`K`에 고립점이 없을 때)
theorem ncard_isolated_map {W : Type*} [Finite W] (K : SimpleGraph W) (f : W ↪ V)
    (hK : ∀ a, ¬ K.IsIsolated a) :
    {v | (K.map f).IsIsolated v}.ncard + Nat.card W = Nat.card V := by
  have hS : {v | (K.map f).IsIsolated v} = (Set.range f)ᶜ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
    constructor
    · rintro hv a rfl
      obtain ⟨b, hab⟩ := exists_adj_iff_not_isIsolated.mpr (hK a)
      exact hv (f b) ((map_adj f K _ _).mpr ⟨a, b, hab, rfl, rfl⟩)
    · intro hv z hvz
      obtain ⟨a, b, -, ha, -⟩ := (map_adj f K _ _).mp hvz
      exact hv a ha
  rw [hS, ← Set.ncard_range_of_injective f.injective, add_comm]
  exact Set.ncard_add_ncard_compl _

omit [Finite V] in
theorem ncard_edgeSet_map {W : Type*} [Finite W] (K : SimpleGraph W) (f : W ↪ V) :
    (K.map f).edgeSet.ncard = K.edgeSet.ncard := by
  rw [edgeSet_map, Set.ncard_image_of_injective _ f.sym2Map.injective]

end Kuratowski
