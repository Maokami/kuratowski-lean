import Kuratowski.Euler
import Kuratowski.Map
import Kuratowski.Planar

/-!
# 비고립 꼭짓점이 네 개 이하인 그래프의 평면성

블루프린트 보조정리 `lem:small`. 비고립 꼭짓점의 집합 `G.support`에 유도한 그래프를
`Fin 4`로 옮기면 `K₄`의 부분 그래프다. `isPlanar_map_iff`를 두 번 써서 원래 그래프로 돌아온다.
고립점 수는 제한하지 않고, 지지 집합과 꼭짓점 타입이 빈 경우도 포함한다.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*} [Finite V]

/-- **지지 집합이 네 개 이하면 평면이다** (블루프린트 `lem:small`).
`G.support`는 고립점이 아닌 꼭짓점의 집합이고, 고립점 수에는 제한이 없다. -/
theorem isPlanar_of_ncard_support_le_four (G : SimpleGraph V) (h : G.support.ncard ≤ 4) :
    IsPlanar G := by
  classical
  let : Fintype G.support := Fintype.ofFinite _
  have hcard : Fintype.card G.support ≤ Fintype.card (Fin 4) := by
    simpa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Nat.card_fin] using h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hmap : IsPlanar ((G.induce G.support).map f) := K4_isPlanar.mono le_top
  have hind : IsPlanar (G.induce G.support) := (isPlanar_map_iff _ f).mp hmap
  have hG := (isPlanar_map_iff (G.induce G.support) (Function.Embedding.subtype _)).mpr hind
  change IsPlanar (G.induce G.support).spanningCoe at hG
  simpa only [spanningCoe_induce_support] using hG

end Kuratowski
