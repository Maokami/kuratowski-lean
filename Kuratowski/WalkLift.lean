import Kuratowski.Contract
import Kuratowski.PathsSubdivision

/-!
# 수축 그래프의 걸음 들어 올리기

`G.Adj x y`일 때 `contractEdge G x y`(`x`를 남기고 `y`는 고립점)의 걸음을 `G`의 걸음으로 옮긴다.
수축 그래프의 변 `u ∼ b`는 `G`의 변이거나, 한쪽이 `x`이고 다른 쪽이 `y`의 이웃이다. 뒤의 경우에는
`u - y - b`로 바꾼다 (`liftWalk`). 경로가 필요하면 `bypass`로 줄인다 (`liftPath`).

분기점 `x`에서 출발하는 경로는 새 분기점 `t ∈ {x, y}`에서 출발하도록 바꾼다 (`exists_liftFrom`).
첫 변이 `t`에 닿지 않을 때만 다른 점(`x`나 `y`)이 하나 끼어든다.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x y : V}

/-- 수축 그래프의 변은 원래 변이거나 `y`를 거치는 두 변이다. -/
theorem adj_or_adj_y_of_contractEdge_adj (hxy : G.Adj x y) {u b : V}
    (h : (contractEdge G x y).Adj u b) : G.Adj u b ∨ (G.Adj u y ∧ G.Adj y b) := by
  rcases h with ⟨-, -, -, h | ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨hxy, h⟩
  · exact Or.inr ⟨h.symm, hxy.symm⟩

/-- `x`에 닿지 않는 수축 그래프의 변은 원래 변이다. -/
theorem adj_of_contractEdge_adj_of_ne {u b : V} (h : (contractEdge G x y).Adj u b)
    (hu : u ≠ x) (hb : b ≠ x) : G.Adj u b := by
  rcases h with ⟨-, -, -, h | ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
  · exact h
  · exact absurd rfl hu
  · exact absurd rfl hb

/-- `x`에서 나가는 수축 그래프의 변의 끝은 `x`나 `y`의 원래 이웃이다. -/
theorem adj_x_or_adj_y_of_contractEdge_adj {b : V} (h : (contractEdge G x y).Adj x b) :
    G.Adj x b ∨ G.Adj y b := by
  rcases h with ⟨hxb, -, -, h | ⟨-, h⟩ | ⟨rfl, -⟩⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd rfl hxb

/-- 수축 그래프의 걸음은 `y`가 아닌 점에서 출발하면 `y`를 지나지 않는다. -/
theorem not_mem_support_contractEdge {u v : V} (q : (contractEdge G x y).Walk u v) (hu : u ≠ y) :
    y ∉ q.support :=
  not_mem_support_of_isIsolated isIsolated_contractEdge q hu

open Classical in
/-- 수축 그래프의 걸음을 변마다 들어 올린 걸음. 원래 변이 아니면 `y`를 거친다. -/
noncomputable def liftWalk (hxy : G.Adj x y) :
    ∀ {u v : V}, (contractEdge G x y).Walk u v → G.Walk u v
  | _, _, .nil => .nil
  | _, _, @Walk.cons _ _ u b _ h p =>
    if hG : G.Adj u b then .cons hG (liftWalk hxy p)
    else
      have h' := (adj_or_adj_y_of_contractEdge_adj hxy h).resolve_left hG
      .cons h'.1 (.cons h'.2 (liftWalk hxy p))

theorem mem_support_liftWalk (hxy : G.Adj x y) {u v : V} (q : (contractEdge G x y).Walk u v)
    {z : V} (hz : z ∈ (liftWalk hxy q).support) : z ∈ q.support ∨ z = y := by
  induction q with
  | nil =>
    simp only [liftWalk, Walk.support_nil, List.mem_singleton] at hz
    exact Or.inl (by simp [hz])
  | @cons u b v h p ih =>
    simp only [liftWalk] at hz
    split_ifs at hz with hG
    · rw [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Or.inl (Walk.start_mem_support _)
      · rcases ih hz with h1 | h1
        · exact Or.inl (by simp [h1])
        · exact Or.inr h1
    · simp only [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | rfl | hz
      · exact Or.inl (Walk.start_mem_support _)
      · exact Or.inr rfl
      · rcases ih hz with h1 | h1
        · exact Or.inl (by simp [h1])
        · exact Or.inr h1

/-- `x`를 지나지 않는 걸음은 그대로 옮겨진다. -/
theorem support_liftWalk_of_not_mem (hxy : G.Adj x y) {u v : V}
    (q : (contractEdge G x y).Walk u v) (hx : x ∉ q.support) :
    (liftWalk hxy q).support = q.support := by
  induction q with
  | nil => rfl
  | @cons u b v h p ih =>
    have hu : u ≠ x := by
      rintro rfl
      exact hx (Walk.start_mem_support _)
    have hb : b ≠ x := by
      rintro rfl
      exact hx (by simp)
    have hpx : x ∉ p.support := fun e ↦ hx (by simp [e])
    have hG := adj_of_contractEdge_adj_of_ne h hu hb
    simp only [liftWalk, hG, ↓reduceDIte, Walk.support_cons, ih hpx]

/-- 들어 올린 걸음을 경로로 줄인 것. -/
noncomputable def liftPath [DecidableEq V] (hxy : G.Adj x y) {u v : V}
    (q : (contractEdge G x y).Walk u v) : G.Walk u v :=
  (liftWalk hxy q).bypass

theorem liftPath_isPath [DecidableEq V] (hxy : G.Adj x y) {u v : V}
    (q : (contractEdge G x y).Walk u v) : (liftPath hxy q).IsPath :=
  Walk.bypass_isPath _

theorem mem_support_liftPath [DecidableEq V] (hxy : G.Adj x y) {u v : V}
    (q : (contractEdge G x y).Walk u v) {z : V} (hz : z ∈ (liftPath hxy q).support) :
    z ∈ q.support ∨ z = y :=
  mem_support_liftWalk hxy q (Walk.support_bypass_subset_support _ hz)

theorem mem_support_liftPath_of_not_mem [DecidableEq V] (hxy : G.Adj x y) {u v : V}
    (q : (contractEdge G x y).Walk u v) (hx : x ∉ q.support) {z : V}
    (hz : z ∈ (liftPath hxy q).support) : z ∈ q.support := by
  have h := Walk.support_bypass_subset_support _ hz
  rwa [support_liftWalk_of_not_mem hxy q hx] at h

/-- 들어 올린 경로의 내부는 원래 내부와 `y`에 들어 있다. -/
theorem walkInterior_liftPath_subset [DecidableEq V] (hxy : G.Adj x y) {u v : V}
    (q : (contractEdge G x y).Walk u v) {z : V} (hz : z ∈ walkInterior (liftPath hxy q)) :
    z ∈ walkInterior q ∨ z = y := by
  rcases mem_support_liftPath hxy q hz.1 with h | h
  · exact Or.inl ⟨h, hz.2⟩
  · exact Or.inr h

/-- `x`를 지나지 않으면 들어 올린 경로의 내부는 원래 내부에 들어 있다. -/
theorem walkInterior_liftPath_subset_of_not_mem [DecidableEq V] (hxy : G.Adj x y) {u v : V}
    (q : (contractEdge G x y).Walk u v) (hx : x ∉ q.support) {z : V}
    (hz : z ∈ walkInterior (liftPath hxy q)) : z ∈ walkInterior q :=
  ⟨mem_support_liftPath_of_not_mem hxy q hx hz.1, hz.2⟩

/-- 분기점 `x`에서 출발하는 경로를 새 분기점 `t ∈ {x, y}`에서 출발하도록 들어 올린다. 첫 변이
`t`에 닿지 않을 때만 `x`나 `y` 가운데 다른 점이 끼어든다. -/
theorem exists_liftFrom [DecidableEq V] (hxy : G.Adj x y) {t : V} (ht : t = x ∨ t = y) {v : V}
    (q : (contractEdge G x y).Walk x v) (hq : q.IsPath) (hv : v ≠ x) :
    ∃ r : G.Walk t v, r.IsPath ∧ ∀ z ∈ r.support,
      z = t ∨ (z ∈ q.support ∧ z ≠ x) ∨ ((z = x ∨ z = y) ∧ ¬ G.Adj t q.snd) := by
  have hn : ¬ q.Nil := Walk.not_nil_of_ne hv.symm
  have hb := q.adj_snd hn
  set b := q.snd with hbdef
  have htail : x ∉ q.tail.support := by
    have := hq
    rw [← q.cons_tail_eq hn, Walk.cons_isPath_iff] at this
    exact this.2
  have htail' : ∀ z ∈ (liftWalk hxy q.tail).support, z ∈ q.support ∧ z ≠ x := by
    intro z hz
    rw [support_liftWalk_of_not_mem hxy _ htail] at hz
    refine ⟨?_, fun e ↦ htail (e ▸ hz)⟩
    rw [← q.cons_tail_eq hn, Walk.support_cons]
    exact List.mem_cons_of_mem _ hz
  by_cases hG : G.Adj t b
  · refine ⟨(Walk.cons hG (liftWalk hxy q.tail)).bypass, Walk.bypass_isPath _, ?_⟩
    intro z hz
    have hz' := Walk.support_bypass_subset_support _ hz
    rw [Walk.support_cons, List.mem_cons] at hz'
    rcases hz' with rfl | hz'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (htail' z hz'))
  · -- 다른 점 `o`를 거친다
    have hto : ∃ o, (o = x ∨ o = y) ∧ G.Adj t o ∧ G.Adj o b := by
      rcases ht with rfl | rfl
      · refine ⟨y, Or.inr rfl, hxy, ?_⟩
        exact (adj_x_or_adj_y_of_contractEdge_adj hb).resolve_left hG
      · refine ⟨x, Or.inl rfl, hxy.symm, ?_⟩
        exact (adj_x_or_adj_y_of_contractEdge_adj hb).resolve_right hG
    obtain ⟨o, ho, hto, hob⟩ := hto
    refine ⟨(Walk.cons hto (Walk.cons hob (liftWalk hxy q.tail))).bypass,
      Walk.bypass_isPath _, ?_⟩
    intro z hz
    have hz' := Walk.support_bypass_subset_support _ hz
    simp only [Walk.support_cons, List.mem_cons] at hz'
    rcases hz' with rfl | rfl | hz'
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨ho, hG⟩)
    · exact Or.inr (Or.inl (htail' z hz'))

end Kuratowski
