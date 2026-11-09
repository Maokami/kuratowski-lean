import Kuratowski.WalkLift
import Kuratowski.ConnectedContraction

/-!
# 수축과 변 추가의 세기

변 수에 대한 강한 귀납법과 꼭짓점 나누기 수술에 필요한 식이다. 변 수축은 변 수를 엄밀히 줄인다.
꼭짓점 타입은 그대로이므로 합쳐진 점은 고립점으로 남아 성분 수가 하나 늘어난다.
남긴 점이 수축 뒤 비고립이면 고립점 수도 하나 늘어난다. 역다트 한 쌍을 뺀 전단사에서의 변 수 식과,
이미 이어진 비고립 두 점 사이에 변을 넣을 때의 세기도 함께 둔다.
-/

namespace Kuratowski
open SimpleGraph
variable {V : Type*} {G H : SimpleGraph V} {x y : V}

/-- `y`가 부분 그래프의 고립점이면 `y`를 합쳐도 그 부분 그래프의 변은 남는다. -/
theorem le_contractEdge_of_isIsolated (hHG : H ≤ G) (hy : H.IsIsolated y) :
    H ≤ contractEdge G x y := by
  intro a b hab
  refine ⟨hab.ne, ?_, ?_, Or.inl (hHG hab)⟩
  · intro e
    subst a
    exact hy b hab
  · intro e
    subst b
    exact hy a hab.symm

/-- 수축 뒤의 변은 `xy`를 뺀 원래 변의 상에 포함된다. -/
theorem edgeSet_contractEdge_subset_image [DecidableEq V] :
    (contractEdge G x y).edgeSet ⊆
      Sym2.map (fun a ↦ if a = y then x else a) '' (G.edgeSet \ {s(x, y)}) := by
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    intro hab
    rcases hab with ⟨hne, hay, hby, hab | ⟨rfl, hab⟩ | ⟨rfl, hab⟩⟩
    · refine ⟨s(a, b), ⟨hab, ?_⟩, ?_⟩
      · simp only [Set.mem_singleton_iff, Sym2.eq_iff]
        rintro (⟨_, rfl⟩ | ⟨rfl, _⟩)
        · exact hby rfl
        · exact hay rfl
      · simp [Sym2.map_mk, hay, hby]
    · refine ⟨s(y, b), ⟨hab, ?_⟩, ?_⟩
      · simp only [Set.mem_singleton_iff, Sym2.eq_iff]
        rintro (⟨_, rfl⟩ | ⟨_, rfl⟩)
        · exact hby rfl
        · exact hne rfl
      · simp [Sym2.map_mk, hby]
    · refine ⟨s(a, y), ⟨hab.symm, ?_⟩, ?_⟩
      · simp only [Set.mem_singleton_iff, Sym2.eq_iff]
        rintro (⟨rfl, _⟩ | ⟨rfl, _⟩)
        · exact hne rfl
        · exact hay rfl
      · simp [Sym2.map_mk, hay]

/-- 실제 변을 수축하면 변 수가 엄밀히 줄어든다. -/
theorem ncard_edgeSet_contractEdge_lt [Finite V] (hxy : G.Adj x y) :
    (contractEdge G x y).edgeSet.ncard < G.edgeSet.ncard := by
  classical
  have hle := Set.ncard_le_ncard (edgeSet_contractEdge_subset_image (G := G) (x := x) (y := y))
  have him := Set.ncard_image_le (f := Sym2.map (fun a ↦ if a = y then x else a))
    (s := G.edgeSet \ {s(x, y)})
  exact lt_of_le_of_lt (hle.trans him) (Set.ncard_sdiff_singleton_lt_of_mem hxy)

end Kuratowski


namespace Kuratowski
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {x y : V}

/-- 수축 그래프에서의 도달은 원래 그래프에서도 도달이다. -/
theorem reachable_of_contractEdge (hxy : G.Adj x y) {a b : V}
    (h : (contractEdge G x y).Reachable a b) : G.Reachable a b := by
  classical
  obtain ⟨p⟩ := h
  exact ⟨liftWalk hxy p⟩

/-- 합쳐져 고립점이 된 `y`를 제외하면 원래 그래프와 수축 그래프의 성분 관계가 같다. -/
theorem reachable_contractEdge_iff (hxy : G.Adj x y) {a b : V} (ha : a ≠ y) (hb : b ≠ y) :
    (contractEdge G x y).Reachable a b ↔ G.Reachable a b := by
  refine ⟨reachable_of_contractEdge hxy, fun h ↦ ?_⟩
  simpa using reachable_contractEdge_of_not_mem (G := G) hxy.ne (S := ∅)
    (by simp) ha hb (by simpa using h)

/-- 고정된 꼭짓점 타입 위에서는 수축이 고립점 `y`의 성분 하나를 더 만든다. -/
theorem card_connectedComponent_contractEdge [Finite V] (hxy : G.Adj x y) :
    Nat.card (contractEdge G x y).ConnectedComponent = Nat.card G.ConnectedComponent + 1 := by
  classical
  let label : V → Option G.ConnectedComponent := fun a ↦
    if a = y then none else some (G.connectedComponentMk a)
  have hlabel : ∀ a b, (contractEdge G x y).Reachable a b → label a = label b := by
    intro a b hab
    by_cases ha : a = y
    · subst a
      have hb := eq_of_isIsolated_of_reachable (isIsolated_contractEdge (G := G) (x := x)) hab
      rw [hb]
    have hb : b ≠ y := by
      intro hb
      subst b
      exact ha (eq_of_isIsolated_of_reachable
        (isIsolated_contractEdge (G := G) (x := x)) hab.symm)
    simp only [label, ha, hb, ↓reduceIte, Option.some.injEq]
    exact ConnectedComponent.sound (reachable_of_contractEdge hxy hab)
  let f : (contractEdge G x y).ConnectedComponent → Option G.ConnectedComponent :=
    ConnectedComponent.lift label (fun a b p _ ↦ hlabel a b p.reachable)
  have hf : Function.Bijective f := by
    constructor
    · intro A B
      induction A using ConnectedComponent.ind with | h a => ?_
      induction B using ConnectedComponent.ind with | h b => ?_
      intro hab
      simp only [f, ConnectedComponent.lift_mk, label] at hab
      by_cases ha : a = y
      · have hb : b = y := by
          by_contra hb
          simp [ha, hb] at hab
        rw [ha, hb]
      have hb : b ≠ y := by
        intro hb
        simp [ha, hb] at hab
      simp only [ha, hb, ↓reduceIte, Option.some.injEq] at hab
      exact ConnectedComponent.sound
        ((reachable_contractEdge_iff hxy ha hb).2 (ConnectedComponent.exact hab))
    · rintro (_ | A)
      · exact ⟨(contractEdge G x y).connectedComponentMk y, by simp [f, label]⟩
      · induction A using ConnectedComponent.ind with | h a => ?_
        by_cases ha : a = y
        · refine ⟨(contractEdge G x y).connectedComponentMk x, ?_⟩
          simp only [f, ConnectedComponent.lift_mk, label, hxy.ne, ↓reduceIte,
            Option.some.injEq]
          rw [ha]
          exact ConnectedComponent.sound hxy.reachable
        · exact ⟨(contractEdge G x y).connectedComponentMk a, by simp [f, label, ha]⟩
  simpa only [Finite.card_option] using Nat.card_eq_of_bijective f hf

/-- `x`, `y`가 아닌 점의 고립 여부는 수축에서 유지된다. -/
theorem isIsolated_contractEdge_iff_of_ne (hxy : x ≠ y) {a : V} (hax : a ≠ x) (hay : a ≠ y) :
    (contractEdge G x y).IsIsolated a ↔ G.IsIsolated a := by
  constructor
  · intro h b hab
    by_cases hby : b = y
    · subst b
      exact h x ⟨hax, hay, hxy, Or.inr (Or.inr ⟨rfl, hab.symm⟩)⟩
    · exact h b ⟨hab.ne, hay, hby, Or.inl hab⟩
  · rintro h b ⟨_, _, _, hab | ⟨rfl, _⟩ | ⟨_, hab⟩⟩
    · exact h b hab
    · exact hax rfl
    · exact h y hab.symm

/-- 수축 뒤 `x`가 고립되지 않으면, 고립점은 `y` 하나만 늘어난다. -/
theorem ncard_isolated_contractEdge [Finite V] (hxy : G.Adj x y)
    (hx : ¬ (contractEdge G x y).IsIsolated x) :
    {a | (contractEdge G x y).IsIsolated a}.ncard = {a | G.IsIsolated a}.ncard + 1 := by
  have hset : {a | (contractEdge G x y).IsIsolated a} = insert y {a | G.IsIsolated a} := by
    ext a
    by_cases hay : a = y
    · subst a
      simp [isIsolated_contractEdge]
    by_cases hax : a = x
    · subst a
      simp only [Set.mem_ofPred_eq, hx, Set.mem_insert_iff, hxy.ne, false_or, false_iff]
      exact fun h ↦ h y hxy
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, hay, false_or]
    exact isIsolated_contractEdge_iff_of_ne hxy.ne hax hay
  have hy : ¬ G.IsIsolated y := fun h ↦ h x hxy.symm
  rw [hset, Set.ncard_insert_of_notMem hy]

end Kuratowski


namespace Kuratowski
open SimpleGraph
variable {V : Type*} [Finite V] {G H : SimpleGraph V}

/-- 서로 역인 두 다트를 뺀 전단사는 변 수를 하나 줄인다. -/
theorem ncard_edgeSet_of_dartEquiv_delete_pair (p : G.Dart)
    (e : {d : G.Dart // d ≠ p ∧ d ≠ p.symm} ≃ H.Dart) :
    G.edgeSet.ncard = H.edgeSet.ncard + 1 := by
  have hc := Set.ncard_add_ncard_compl ({p, p.symm} : Set G.Dart)
  have heq : ({p, p.symm} : Set G.Dart)ᶜ = {d | d ≠ p ∧ d ≠ p.symm} := by
    ext d
    simp
  rw [Set.ncard_pair (Dart.symm_ne p).symm, heq] at hc
  change 2 + Nat.card {d : G.Dart // d ≠ p ∧ d ≠ p.symm} = Nat.card G.Dart at hc
  rw [Nat.card_congr e, card_dart_eq, card_dart_eq] at hc
  omega

/-- 없던 변을 하나 넣으면 변 수가 하나 늘어난다. -/
theorem ncard_edgeSet_sup_edge {a b : V} (hab : a ≠ b) (hn : ¬ G.Adj a b) :
    (G ⊔ edge a b).edgeSet.ncard = G.edgeSet.ncard + 1 := by
  have heq : (G ⊔ edge a b).edgeSet = insert s(a, b) G.edgeSet := by
    rw [edgeSet_sup, edgeSet_edge_of_ne hab, Set.union_singleton]
  have hnot : s(a, b) ∉ G.edgeSet := hn
  rw [heq, Set.ncard_insert_of_notMem hnot]

omit [Finite V] in
/-- 이미 비고립인 두 점 사이에 변을 넣어도 고립점 수는 같다. -/
theorem ncard_isolated_sup_edge {a b : V} (ha : ¬ G.IsIsolated a) (hb : ¬ G.IsIsolated b) :
    {v | (G ⊔ edge a b).IsIsolated v}.ncard = {v | G.IsIsolated v}.ncard := by
  congr 1
  ext v
  constructor
  · intro hv w hvw
    exact hv w (Or.inl hvw)
  · intro hv w hvw
    rcases hvw with hvw | hvw
    · exact hv w hvw
    · rcases (edge_adj a b v w).1 hvw with ⟨⟨rfl, _⟩ | ⟨rfl, _⟩, _⟩
      · exact ha hv
      · exact hb hv

omit [Finite V] in
/-- 이미 이어진 두 점 사이에 변을 넣어도 성분 수는 같다. -/
theorem card_connectedComponent_sup_edge_of_reachable {a b : V} (hab : G.Reachable a b) :
    Nat.card (G ⊔ edge a b).ConnectedComponent = Nat.card G.ConnectedComponent := by
  have hreach : ∀ u v, (G ⊔ edge a b).Reachable u v ↔ G.Reachable u v := by
    intro u v
    refine ⟨?_, fun h ↦ h.mono le_sup_left⟩
    apply reachable_of_forall_adj id
    intro u v huv
    rcases huv with huv | huv
    · exact huv.reachable
    · rcases (edge_adj a b u v).1 huv with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
      · exact hab
      · exact hab.symm
  exact Nat.card_congr (Quot.congr (Equiv.refl V) hreach)

end Kuratowski


