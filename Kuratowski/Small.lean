import Kuratowski.Euler
import Kuratowski.Map
import Kuratowski.Planar

/-!
# Planarity of finite graphs with at most four non-isolated vertices

Blueprint lemma `lem:small`. The graph induced on the set `G.support` of non-isolated vertices,
transported to `Fin 4`, is a subgraph of `K₄`. Two applications of `isPlanar_map_iff` return to the
original graph. The number of isolated vertices is not restricted, and empty supports and empty
vertex types are included.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*} [Finite V]

/-- **A finite graph with at most four support vertices is planar** (blueprint `lem:small`).
`G.support` is the set of non-isolated vertices; the number of isolated vertices is not
restricted. -/
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
