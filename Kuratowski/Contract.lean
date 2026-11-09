import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# 변 수축

블루프린트 정의 `def:contract`. `G/xy`는 `y`를 `x`에 합친 그래프다. 꼭짓점 타입 `V`는 그대로 두고,
`y`는 고립점이 된다. 겹친 변은 하나로 친다 (단순 그래프).

정의는 모든 `x`, `y`에 대해 주어지지만, 실제 변 수축은 `G.Adj x y`(따라서 `x ≠ y`)를 가정한다.
`x = y`이면 `y`에 닿는 변을 모두 지운 그래프가 된다 (`contractEdge_self_adj`).
`scripts/check_blueprint.py`의 `contract`와는 `x ≠ y`이면 늘 같고, `x = y`이면 일반적으로 다르다
(Lean은 `x`에 닿는 변을 지우고 Python은 `G`를 그대로 둔다). 변·고립점·성분 수는
`ContractCounts.lean`에서 별도로 다룬다.
-/

namespace Kuratowski
open SimpleGraph

variable {V : Type*}

/-- 변 `xy`를 수축한 그래프 `G/xy`. `p ≠ q`이고 `p, q ≠ y`일 때 `p ∼ q`는 원래 인접이거나,
한쪽이 `x`이고 다른 쪽이 `y`의 이웃인 경우다. `p ≠ q` 조건이 고리 `xx`를 막는다. -/
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

/-- 합쳐진 꼭짓점 `y`는 고립점이다. -/
theorem isIsolated_contractEdge : (contractEdge G x y).IsIsolated y :=
  fun _ h => h.2.1 rfl

/-- `x ≠ y`이면 `x`의 새 이웃은 `x`나 `y`의 이웃 가운데 `x`, `y`가 아닌 것이다. -/
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

/-- `x ≠ y`이면 `N_{G/xy}(x) = (N_G(x) ∪ N_G(y)) \ {x, y}`. -/
theorem neighborSet_contractEdge_left (hxy : x ≠ y) :
    (contractEdge G x y).neighborSet x = (G.neighborSet x ∪ G.neighborSet y) \ {x, y} := by
  ext q
  simp only [mem_neighborSet, contractEdge_adj_left hxy, Set.mem_sdiff, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  tauto

/-- `x`, `y`가 아닌 두 꼭짓점 사이의 인접은 수축해도 그대로다. -/
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

/-- `x = y`일 때의 동작: `x`에 닿는 변을 모두 지운다. 실제 수축(`G.Adj x y`)에서는 생기지 않는다. -/
theorem contractEdge_self_adj : (contractEdge G x x).Adj p q ↔ p ≠ x ∧ q ≠ x ∧ G.Adj p q := by
  rw [contractEdge_adj]
  constructor
  · rintro ⟨-, hp, hq, h | ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    · exact ⟨hp, hq, h⟩
    · exact absurd rfl hp
    · exact absurd rfl hq
  · rintro ⟨hp, hq, h⟩
    exact ⟨G.ne_of_adj h, hp, hq, Or.inl h⟩

/-- 예: `K₄`에서 변 `01`을 수축하면 `1`은 고립점이고 `0`, `2`, `3`은 삼각형을 이룬다.
`scripts/check_blueprint.py`의 `contract(4, K4, 0, 1)`과 같다. -/
theorem contractEdge_top_zero_one (p q : Fin 4) :
    (contractEdge (⊤ : SimpleGraph (Fin 4)) 0 1).Adj p q ↔ p ≠ q ∧ p ≠ 1 ∧ q ≠ 1 := by
  revert p q
  decide +kernel

end Kuratowski
