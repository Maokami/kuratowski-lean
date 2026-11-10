import Kuratowski.Euler
import Kuratowski.Smoothing
import Kuratowski.NonPlanar

/-!
# Kuratowski's theorem: the easy direction

> A finite graph containing a subdivision of `K₅` or `K₃,₃` as a subgraph is not planar.

Planarity is the combinatorial definition of `Kuratowski/Basic.lean` (a rotation system of
genus 0).

## Subdivisions

A **subdivision** of a graph `K` (vertices `W`) is obtained by repeatedly splitting an edge of `K`
with a new vertex (`TX` in Diestel, *Graph Theory*, Section 1.7). Since we work inside a larger
graph `G` (vertices `V`), we start by placing the vertices of `K` in `V` via `f : W ↪ V`
(`K.map f`; the other vertices are isolated). One step splits an edge `xy` of the current graph `H`
with an unused vertex `w`: `w` is not a vertex position of `K` (`w ∉ Set.range f`) and meets no
edge of `H` (`H.IsIsolated w`).

`G` contains a subdivision of `K` if some such subdivision `H` is a subgraph of `G` (`H ≤ G`).
For finite graphs this agrees with the usual notion of `K` being a topological minor of `G`.

## Proof

* If `G` is planar, so is its subgraph `H` (`IsPlanar.mono`, via Euler's inequality).
* Undoing one subdivision step preserves planarity (`IsPlanar.of_subdivideEdge`), so `K.map f` is
  planar.
* But `K₅.map f` and `K₃,₃.map f` are not planar by face counting.
-/

namespace Kuratowski

open SimpleGraph

variable {V W : Type*}

/-- `H` is a subdivision of `K` whose vertices are placed at the positions given by `f`. -/
inductive IsSubdivision (K : SimpleGraph W) : (W ↪ V) → SimpleGraph V → Prop
  /-- `K` itself (with vertices transported by `f`). -/
  | map (f : W ↪ V) : IsSubdivision K f (K.map f)
  /-- Split an edge `xy` with an unused vertex `w`. -/
  | subdivide {f : W ↪ V} {H : SimpleGraph V} {x y w : V} :
      IsSubdivision K f H → H.Adj x y → w ∉ Set.range f → H.IsIsolated w →
      IsSubdivision K f (subdivideEdge H x y w)

/-- `G` contains a subdivision of `K` as a subgraph. For finite graphs this means that `K` is a
topological minor of `G`. -/
def ContainsSubdivision (G : SimpleGraph V) (K : SimpleGraph W) : Prop :=
  ∃ (f : W ↪ V) (H : SimpleGraph V), IsSubdivision K f H ∧ H ≤ G

variable [Finite V] [DecidableEq V]

/-- Undoing a planar subdivision gives a planar graph. -/
theorem IsSubdivision.isPlanar_map {K : SimpleGraph W} {f : W ↪ V} {H : SimpleGraph V}
    (hS : IsSubdivision K f H) (hH : IsPlanar H) : IsPlanar (K.map f) := by
  induction hS with
  | map => exact hH
  | subdivide _ hxy _ hw ih => exact ih (hH.of_subdivideEdge hxy hw)

/-- If a planar graph contains a subdivision of `K`, then `K.map f` is planar for some `f`. -/
theorem IsPlanar.isPlanar_map_of_containsSubdivision {G : SimpleGraph V} {K : SimpleGraph W}
    (hG : IsPlanar G) (h : ContainsSubdivision G K) : ∃ f : W ↪ V, IsPlanar (K.map f) := by
  obtain ⟨f, H, hS, hle⟩ := h
  exact ⟨f, hS.isPlanar_map (hG.mono hle)⟩

/-- **Kuratowski's theorem (easy direction)**: a finite graph containing a subdivision of `K₅` or
`K₃,₃` is not planar. Planarity is the combinatorial definition of `Kuratowski/Basic.lean`
(a rotation system of genus 0). -/
theorem not_isPlanar_of_containsSubdivision {G : SimpleGraph V}
    (h : ContainsSubdivision G K5 ∨ ContainsSubdivision G K33) : ¬ IsPlanar G := by
  intro hG
  rcases h with h | h
  · obtain ⟨f, hf⟩ := hG.isPlanar_map_of_containsSubdivision h
    exact K5_map_not_isPlanar f hf
  · obtain ⟨f, hf⟩ := hG.isPlanar_map_of_containsSubdivision h
    exact K33_map_not_isPlanar f hf

/-- The contrapositive: a planar graph contains no subdivision of `K₅` and no subdivision of
`K₃,₃`. -/
theorem IsPlanar.not_containsSubdivision {G : SimpleGraph V} (hG : IsPlanar G) :
    ¬ ContainsSubdivision G K5 ∧ ¬ ContainsSubdivision G K33 :=
  ⟨fun h => not_isPlanar_of_containsSubdivision (Or.inl h) hG,
    fun h => not_isPlanar_of_containsSubdivision (Or.inr h) hG⟩

end Kuratowski
