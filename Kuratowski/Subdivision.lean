import Kuratowski.Euler
import Kuratowski.Smoothing
import Kuratowski.NonPlanar

/-!
# 쿠라토프스키 정리: 쉬운 방향

> 유한 그래프가 `K₅`나 `K₃,₃`의 세분을 부분 그래프로 가지면 평면 그래프가 아니다.

평면성은 `Kuratowski/Basic.lean`의 조합적 정의(종수 0인 회전 체계)를 쓴다.

## 세분의 정의

그래프 `K`(꼭짓점 `W`)의 **세분**(subdivision)은 `K`의 변을 하나씩 새 꼭짓점으로 나누어 얻는
그래프다 (Diestel, *Graph Theory*, 1.7절의 `TX`). 큰 그래프 `G`(꼭짓점 `V`) 안에서 생각하므로
`K`의 꼭짓점을 `f : W ↪ V`로 `V`에 놓고 시작한다 (`K.map f`, 나머지 꼭짓점은 고립점).
한 단계에서는 지금 그래프 `H`의 변 `xy`를 아직 쓰이지 않은 꼭짓점 `w`로 나눈다.
`w`는 `K`의 꼭짓점 자리가 아니고 (`w ∉ Set.range f`) `H`의 어느 변에도 닿지 않는다
(`H.IsIsolated w`).

`G`가 `K`의 세분을 포함한다는 것은 그런 세분 `H`가 `G`의 부분 그래프라는 것이다 (`H ≤ G`).
이는 `K`가 `G`의 위상 소수(topological minor)라는 것과 같다.

## 증명

* `G`가 평면이면 부분 그래프 `H`도 평면이다 (`IsPlanar.mono`, 오일러 부등식 사용).
* 세분 한 단계를 되돌려도 평면성이 유지되므로 (`IsPlanar.of_subdivideEdge`), `K.map f`도 평면이다.
* 그런데 `K₅.map f`, `K₃,₃.map f`는 면 수 세기로 평면이 아니다.
-/

namespace Kuratowski

open SimpleGraph

variable {V W : Type*}

/-- `H`는 `K`의 세분이고, `K`의 꼭짓점은 `f`의 자리에 놓여 있다. -/
inductive IsSubdivision (K : SimpleGraph W) : (W ↪ V) → SimpleGraph V → Prop
  /-- `K` 자체 (꼭짓점을 `f`로 옮긴 것). -/
  | map (f : W ↪ V) : IsSubdivision K f (K.map f)
  /-- 변 `xy`를 아직 쓰이지 않은 꼭짓점 `w`로 나눈다. -/
  | subdivide {f : W ↪ V} {H : SimpleGraph V} {x y w : V} :
      IsSubdivision K f H → H.Adj x y → w ∉ Set.range f → H.IsIsolated w →
      IsSubdivision K f (subdivideEdge H x y w)

/-- `G`는 `K`의 세분을 부분 그래프로 갖는다 (`K`는 `G`의 위상 소수다). -/
def ContainsSubdivision (G : SimpleGraph V) (K : SimpleGraph W) : Prop :=
  ∃ (f : W ↪ V) (H : SimpleGraph V), IsSubdivision K f H ∧ H ≤ G

variable [Finite V] [DecidableEq V]

/-- 평면 그래프인 세분을 되돌리면 평면 그래프다. -/
theorem IsSubdivision.isPlanar_map {K : SimpleGraph W} {f : W ↪ V} {H : SimpleGraph V}
    (hS : IsSubdivision K f H) (hH : IsPlanar H) : IsPlanar (K.map f) := by
  induction hS with
  | map => exact hH
  | subdivide _ hxy _ hw ih => exact ih (hH.of_subdivideEdge hxy hw)

/-- 평면 그래프가 `K`의 세분을 포함하면, 어떤 `f`에 대해 `K.map f`도 평면이다. -/
theorem IsPlanar.isPlanar_map_of_containsSubdivision {G : SimpleGraph V} {K : SimpleGraph W}
    (hG : IsPlanar G) (h : ContainsSubdivision G K) : ∃ f : W ↪ V, IsPlanar (K.map f) := by
  obtain ⟨f, H, hS, hle⟩ := h
  exact ⟨f, hS.isPlanar_map (hG.mono hle)⟩

/-- **쿠라토프스키 정리 (쉬운 방향)**: `K₅`나 `K₃,₃`의 세분을 포함하는 유한 그래프는 평면 그래프가
아니다. 평면성은 `Kuratowski/Basic.lean`의 조합적 정의(종수 0인 회전 체계)다. -/
theorem not_isPlanar_of_containsSubdivision {G : SimpleGraph V}
    (h : ContainsSubdivision G K5 ∨ ContainsSubdivision G K33) : ¬ IsPlanar G := by
  intro hG
  rcases h with h | h
  · obtain ⟨f, hf⟩ := hG.isPlanar_map_of_containsSubdivision h
    exact K5_map_not_isPlanar f hf
  · obtain ⟨f, hf⟩ := hG.isPlanar_map_of_containsSubdivision h
    exact K33_map_not_isPlanar f hf

/-- 같은 내용의 대우: 평면 그래프는 `K₅`의 세분도 `K₃,₃`의 세분도 포함하지 않는다. -/
theorem IsPlanar.not_containsSubdivision {G : SimpleGraph V} (hG : IsPlanar G) :
    ¬ ContainsSubdivision G K5 ∧ ¬ ContainsSubdivision G K33 :=
  ⟨fun h => not_isPlanar_of_containsSubdivision (Or.inl h) hG,
    fun h => not_isPlanar_of_containsSubdivision (Or.inr h) hG⟩

end Kuratowski
