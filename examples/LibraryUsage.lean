import Kuratowski.Hard

/-! Public API examples: the full theorem, a planar graph, and a non-planar graph. -/

open SimpleGraph Kuratowski

example {V : Type*} [Finite V] (G : SimpleGraph V) :
    IsPlanar G ↔ ¬ ContainsSubdivision G K5 ∧ ¬ ContainsSubdivision G K33 :=
  isPlanar_iff_kuratowskiFree

example : IsPlanar K4 := K4_isPlanar

example : ¬ IsPlanar K5 := K5_not_isPlanar
