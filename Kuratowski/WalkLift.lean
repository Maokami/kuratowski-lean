import Kuratowski.Contract
import Kuratowski.PathsSubdivision

/-!
# Lifting walks of the contracted graph

For `G.Adj x y`, we transport walks of `contractEdge G x y` (which keeps `x` and isolates `y`) to
walks of `G`. An edge `u ∼ b` of the contracted graph is an edge of `G`, or one end is `x` and the
other is a neighbor of `y`; in the latter case it is replaced by `u - y - b` (`liftWalk`). When a
path is needed, `bypass` shortens the lift (`liftPath`).

A path starting at the branch vertex `x` is changed to start at a new branch vertex `t ∈ {x, y}`
(`exists_liftFrom`). The other vertex (`x` or `y`) is inserted only when the first edge does not
meet `t`.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x y : V}

/-- An edge of the contracted graph is an original edge or a pair of edges through `y`. -/
theorem adj_or_adj_y_of_contractEdge_adj (hxy : G.Adj x y) {u b : V}
    (h : (contractEdge G x y).Adj u b) : G.Adj u b ∨ (G.Adj u y ∧ G.Adj y b) := by
  rcases h with ⟨-, -, -, h | ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨hxy, h⟩
  · exact Or.inr ⟨h.symm, hxy.symm⟩

/-- An edge of the contracted graph not meeting `x` is an original edge. -/
theorem adj_of_contractEdge_adj_of_ne {u b : V} (h : (contractEdge G x y).Adj u b)
    (hu : u ≠ x) (hb : b ≠ x) : G.Adj u b := by
  rcases h with ⟨-, -, -, h | ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
  · exact h
  · exact absurd rfl hu
  · exact absurd rfl hb

/-- The other end of an edge of the contracted graph at `x` is an original neighbor of `x` or of
`y`. -/
theorem adj_x_or_adj_y_of_contractEdge_adj {b : V} (h : (contractEdge G x y).Adj x b) :
    G.Adj x b ∨ G.Adj y b := by
  rcases h with ⟨hxb, -, -, h | ⟨-, h⟩ | ⟨rfl, -⟩⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd rfl hxb

/-- A walk of the contracted graph starting at a vertex other than `y` does not pass through
`y`. -/
theorem not_mem_support_contractEdge {u v : V} (q : (contractEdge G x y).Walk u v) (hu : u ≠ y) :
    y ∉ q.support :=
  not_mem_support_of_isIsolated isIsolated_contractEdge q hu

open Classical in
/-- Lift a walk of the contracted graph edge by edge. Edges that are not original edges pass
through `y`. -/
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

/-- A walk avoiding `x` is transported unchanged. -/
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

/-- The lifted walk shortened to a path. -/
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

/-- The interior of a lifted path lies in the original interior together with `y`. -/
theorem walkInterior_liftPath_subset [DecidableEq V] (hxy : G.Adj x y) {u v : V}
    (q : (contractEdge G x y).Walk u v) {z : V} (hz : z ∈ walkInterior (liftPath hxy q)) :
    z ∈ walkInterior q ∨ z = y := by
  rcases mem_support_liftPath hxy q hz.1 with h | h
  · exact Or.inl ⟨h, hz.2⟩
  · exact Or.inr h

/-- If the walk avoids `x`, the interior of the lifted path lies in the original interior. -/
theorem walkInterior_liftPath_subset_of_not_mem [DecidableEq V] (hxy : G.Adj x y) {u v : V}
    (q : (contractEdge G x y).Walk u v) (hx : x ∉ q.support) {z : V}
    (hz : z ∈ walkInterior (liftPath hxy q)) : z ∈ walkInterior q :=
  ⟨mem_support_liftPath_of_not_mem hxy q hx hz.1, hz.2⟩

/-- Lift a path starting at the branch vertex `x` to a path starting at the new branch vertex
`t ∈ {x, y}`. The vertex of `{x, y}` other than `t` is inserted only when the first edge does not
meet `t`. -/
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
  · -- pass through the other vertex `o`
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
