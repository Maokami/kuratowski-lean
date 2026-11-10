import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Path systems of subdivisions

Blueprint definition `def:paths`. A path system of a graph `K` (vertices `W`) in `G` (vertices `V`)
consists of branch vertices `branch : W ↪ V` and, for each edge `ab` of `K`, a path in `G` from
`branch a` to `branch b`.

* The path in the opposite direction is the reversed path (`path_symm`, `P_ba = P_ab⁻¹` in the
  blueprint).
* Interior vertices of a path are not branch vertices (`interior_not_branch`).
* Paths of two distinct edges (compared as `Sym2`) share no interior vertex (`disjoint`).

Nothing is required for two vertices that are not adjacent in `K`, so `G` may contain further edges
(chords) between branch vertices. The equivalence with the inductive subdivision definition
`IsSubdivision` (`thm:paths_iff`) is in `PathsSubdivision.lean` (forward direction) and
`SubdivisionOfPaths.lean` (reverse direction for finite `V`, and for finite `W` via
`exists_isSubdivision_le_of_finite`).
-/

namespace Kuratowski

open SimpleGraph

variable {V W : Type*}

/-! ### Interior vertices of walks -/

/-- The interior vertices of a walk: visited vertices other than the two endpoints. For a path
these are all vertices except the endpoints. -/
def walkInterior {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

theorem mem_walkInterior {G : SimpleGraph V} {u v x : V} {p : G.Walk u v} :
    x ∈ walkInterior p ↔ x ∈ p.support ∧ x ≠ u ∧ x ≠ v := Iff.rfl

/-- Reversing a walk does not change its interior vertices. -/
@[simp] theorem walkInterior_reverse {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    walkInterior p.reverse = walkInterior p := by
  ext x
  simp only [mem_walkInterior, Walk.support_reverse, List.mem_reverse]
  tauto

/-- A single-edge walk has no interior vertices. -/
@[simp] theorem walkInterior_cons_nil {G : SimpleGraph V} {u v : V} (h : G.Adj u v) :
    walkInterior (Walk.cons h Walk.nil) = ∅ := by
  ext x
  simp only [mem_walkInterior, Walk.support_cons, Walk.support_nil, List.mem_cons,
    List.not_mem_nil, or_false, Set.mem_empty_iff_false, iff_false]
  tauto

/-! ### Path systems -/

/-- A path system of `K` (vertices `W`) in `G` (vertices `V`) (blueprint `def:paths`). -/
structure SubdivisionPaths (K : SimpleGraph W) (G : SimpleGraph V) where
  /-- Branch vertices: the vertices of `K` placed at distinct vertices of `G`. -/
  branch : W ↪ V
  /-- For each edge `ab` of `K`, a walk in `G` from `branch a` to `branch b`. -/
  path : ∀ a b, K.Adj a b → G.Walk (branch a) (branch b)
  /-- Each walk is a path (it repeats no vertex). -/
  isPath : ∀ a b (h : K.Adj a b), (path a b h).IsPath
  /-- The path in the opposite direction is the reversed path. -/
  path_symm : ∀ a b (h : K.Adj a b), path b a h.symm = (path a b h).reverse
  /-- Interior vertices of a path are not branch vertices. -/
  interior_not_branch :
    ∀ a b (h : K.Adj a b), ∀ x ∈ walkInterior (path a b h), x ∉ Set.range branch
  /-- Paths of two distinct edges share no interior vertex. -/
  disjoint : ∀ a b (h : K.Adj a b) c d (h' : K.Adj c d), s(a, b) ≠ s(c, d) →
    Disjoint (walkInterior (path a b h)) (walkInterior (path c d h'))

namespace SubdivisionPaths

variable {K : SimpleGraph W} {G : SimpleGraph V}

/-- Adjacent vertices of `K` have distinct branch vertices. -/
theorem branch_ne (P : SubdivisionPaths K G) {a b : W} (h : K.Adj a b) :
    P.branch a ≠ P.branch b :=
  P.branch.injective.ne h.ne

/-- The paths in the two directions have the same interior. -/
theorem walkInterior_path_symm (P : SubdivisionPaths K G) {a b : W} (h : K.Adj a b) :
    walkInterior (P.path b a h.symm) = walkInterior (P.path a b h) := by
  rw [P.path_symm, walkInterior_reverse]

/-- The unsubdivided case: if `K.map f ≤ G`, there is a path system using one edge of `G` for
each edge of `K`. `G` may have further edges. -/
def ofMapLE (f : W ↪ V) (hle : K.map f ≤ G) : SubdivisionPaths K G where
  branch := f
  path a b h := Walk.cons (hle (map_adj_apply.2 h)) Walk.nil
  isPath a b h := by
    rw [Walk.cons_isPath_iff]
    exact ⟨Walk.IsPath.nil, by simpa using f.injective.ne h.ne⟩
  path_symm _ _ _ := rfl
  interior_not_branch a b h x hx := by simp at hx
  disjoint a b h c d h' _ := by simp

@[simp] theorem ofMapLE_branch (f : W ↪ V) (hle : K.map f ≤ G) : (ofMapLE f hle).branch = f := rfl

end SubdivisionPaths

end Kuratowski
