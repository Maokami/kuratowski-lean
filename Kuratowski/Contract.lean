import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Edge contraction

`contractEdge G x y` identifies `y` with `x` while retaining the vertex type:
`y` becomes isolated, parallel edges are identified, and loops are removed.
Edge contraction uses `G.Adj x y`, hence `x ≠ y`.

For `x = y`, the definition deletes all edges incident to `x`. The Python checker
(`scripts/check_blueprint.py`) instead returns `G` in this degenerate case;
the definitions agree whenever `x ≠ y`.
`ContractCounts` proves the edge, isolated-vertex, and component counts.
`contractVertex` is the associated vertex map, `y ↦ x`.
Blueprint: `def:contract`.
-/

namespace Kuratowski
open SimpleGraph

variable {V : Type*}

/-- Contract `y` into `x`, leaving `y` isolated. For distinct `p, q ≠ y`, adjacency
means `G.Adj p q`, or one endpoint is `x` and the other is a neighbor of `y`. -/
def contractEdge (G : SimpleGraph V) (x y : V) : SimpleGraph V where
  Adj p q := p ≠ q ∧ p ≠ y ∧ q ≠ y ∧ (G.Adj p q ∨ (p = x ∧ G.Adj y q) ∨ (q = x ∧ G.Adj y p))
  symm := ⟨fun p q => by
    rintro ⟨hpq, hp, hq, h | ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
    · exact ⟨hpq.symm, hq, hp, Or.inl h.symm⟩
    · exact ⟨hpq.symm, hq, hp, Or.inr (Or.inr ⟨rfl, h⟩)⟩
    · exact ⟨hpq.symm, hq, hp, Or.inr (Or.inl ⟨rfl, h⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {G : SimpleGraph V} {x y p q : V}

theorem contractEdge_adj :
    (contractEdge G x y).Adj p q ↔
      p ≠ q ∧ p ≠ y ∧ q ≠ y ∧ (G.Adj p q ∨ (p = x ∧ G.Adj y q) ∨ (q = x ∧ G.Adj y p)) :=
  Iff.rfl

instance [DecidableEq V] [DecidableRel G.Adj] : DecidableRel (contractEdge G x y).Adj :=
  fun _ _ => decidable_of_iff' _ contractEdge_adj

/-- The absorbed vertex `y` is isolated. -/
theorem isIsolated_contractEdge : (contractEdge G x y).IsIsolated y :=
  fun _ h => h.2.1 rfl

/-- For `x ≠ y`, take the old neighbors of either endpoint, excluding both endpoints. -/
theorem contractEdge_adj_left (hxy : x ≠ y) :
    (contractEdge G x y).Adj x q ↔ q ≠ x ∧ q ≠ y ∧ (G.Adj x q ∨ G.Adj y q) := by
  rw [contractEdge_adj]
  constructor
  · rintro ⟨hxq, -, hq, h | ⟨-, h⟩ | ⟨rfl, -⟩⟩
    · exact ⟨Ne.symm hxq, hq, Or.inl h⟩
    · exact ⟨Ne.symm hxq, hq, Or.inr h⟩
    · exact absurd rfl hxq
  · rintro ⟨hqx, hq, h | h⟩
    · exact ⟨Ne.symm hqx, hxy, hq, Or.inl h⟩
    · exact ⟨Ne.symm hqx, hxy, hq, Or.inr (Or.inl ⟨rfl, h⟩)⟩

/-- For `x ≠ y`, `N_{G/xy}(x) = (N_G(x) ∪ N_G(y)) \ {x, y}`. -/
theorem neighborSet_contractEdge_left (hxy : x ≠ y) :
    (contractEdge G x y).neighborSet x = (G.neighborSet x ∪ G.neighborSet y) \ {x, y} := by
  ext q
  simp only [mem_neighborSet, contractEdge_adj_left hxy, Set.mem_sdiff, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  tauto

/-- Adjacency between vertices outside `{x, y}` is unchanged. -/
theorem contractEdge_adj_of_ne (hpx : p ≠ x) (hpy : p ≠ y) (hqx : q ≠ x) (hqy : q ≠ y) :
    (contractEdge G x y).Adj p q ↔ G.Adj p q := by
  rw [contractEdge_adj]
  constructor
  · rintro ⟨-, -, -, h | ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    · exact h
    · exact absurd rfl hpx
    · exact absurd rfl hqx
  · intro h
    exact ⟨G.ne_of_adj h, hpy, hqy, Or.inl h⟩

/-- For `x = y`, delete all edges incident to `x`. This case cannot satisfy `G.Adj x y`. -/
theorem contractEdge_self_adj : (contractEdge G x x).Adj p q ↔ p ≠ x ∧ q ≠ x ∧ G.Adj p q := by
  rw [contractEdge_adj]
  constructor
  · rintro ⟨-, hp, hq, h | ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    · exact ⟨hp, hq, h⟩
    · exact absurd rfl hp
    · exact absurd rfl hq
  · rintro ⟨hp, hq, h⟩
    exact ⟨G.ne_of_adj h, hp, hq, Or.inl h⟩

/-- Contracting `01` in `K₄` leaves an isolated `1` and a triangle on `{0, 2, 3}`.
This agrees with `contract(4, K4, 0, 1)` in the Python checker. -/
theorem contractEdge_top_zero_one (p q : Fin 4) :
    (contractEdge (⊤ : SimpleGraph (Fin 4)) 0 1).Adj p q ↔ p ≠ q ∧ p ≠ 1 ∧ q ≠ 1 := by
  revert p q
  decide +kernel

/-- The vertex map identifying `y` with `x`. -/
def contractVertex [DecidableEq V] (x y a : V) : V := if a = y then x else a

lemma contractEdge_adj_contractVertex [DecidableEq V] (hxy : x ≠ y) {a b : V}
    (ha : a ≠ x) (hb : b ≠ x) (hab : G.Adj a b) :
    (contractEdge G x y).Adj (contractVertex x y a) (contractVertex x y b) := by
  by_cases hay : a = y
  · subst a
    have hby : b ≠ y := hab.ne.symm
    simp only [contractVertex, ↓reduceIte, hby]
    exact ⟨hb.symm, hxy, hby, Or.inr (Or.inl ⟨rfl, hab⟩)⟩
  by_cases hby : b = y
  · subst b
    have hay' : a ≠ y := hab.ne
    simp only [contractVertex, hay', ↓reduceIte]
    exact ⟨ha, hay', hxy, Or.inr (Or.inr ⟨rfl, hab.symm⟩)⟩
  simp only [contractVertex, hay, hby, ↓reduceIte]
  exact ⟨hab.ne, hay, hby, Or.inl hab⟩

theorem contractVertex_of_ne [DecidableEq V] {x y p : V} (h : p ≠ y) :
    contractVertex x y p = p := by
  simp [contractVertex, h]

theorem contractVertex_self [DecidableEq V] {x y : V} : contractVertex x y y = x := by
  simp [contractVertex]

theorem contractVertex_eq_cases [DecidableEq V] {x y p q : V}
    (h : contractVertex x y p = contractVertex x y q) :
    p = q ∨ (p = y ∧ q = x) ∨ (p = x ∧ q = y) := by
  unfold contractVertex at h
  by_cases hp : p = y <;> by_cases hq : q = y <;> simp only [hp, hq, ↓reduceIte] at h
  · exact Or.inl (hp.trans hq.symm)
  · exact Or.inr (Or.inl ⟨hp, h.symm⟩)
  · exact Or.inr (Or.inr ⟨h, hq⟩)
  · exact Or.inl h

theorem contractVertex_eq_x [DecidableEq V] {x y p : V} (h : contractVertex x y p = x) :
    p = x ∨ p = y := by
  by_cases hp : p = y
  · exact Or.inr hp
  · rw [contractVertex_of_ne hp] at h
    exact Or.inl h

end Kuratowski
