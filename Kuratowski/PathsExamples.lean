import Kuratowski.Paths
import Kuratowski.ConnectedExamples

/-!
# Examples of path systems

Small examples for blueprint definition `def:paths`, using the graphs `path3` (the path `0 - 1 - 2`)
and `star` (center `0`, leaves `1, 2, 3`) from `ConnectedExamples`.

* Positive example: a path system of `K₂` (vertices `Bool`) in `path3` along `0 → 1 → 2`. The
  interior of the path is `{1}`, which is nonempty, and the path in the opposite direction is the
  reversed path with the same interior.
* Negative examples (finite facts about candidate walks): the walk `1 → 0 → 2` in `star` has `0` in
  its interior, so it violates `interior_not_branch` if `0` is a branch vertex. The walks
  `1 → 0 → 2` and `1 → 0 → 3` share the interior vertex `0`, so using them for two distinct edges
  violates `disjoint`. We do not prove the general claim that the star contains no path system of
  `K₃`.
-/

namespace Kuratowski.PathsExamples

open SimpleGraph Kuratowski.ConnectedExamples

/-! ### Positive example -/

/-- The walk `0 → 1 → 2` in `path3`. -/
def walk012 : path3.Walk 0 2 :=
  .cons (show path3.Adj 0 1 by decide) (.cons (show path3.Adj 1 2 by decide) .nil)

theorem walkInterior_walk012 : walkInterior walk012 = {1} := by
  ext x
  simp only [mem_walkInterior, walk012, Walk.support_cons, Walk.support_nil,
    Set.mem_singleton_iff]
  revert x
  decide

/-- The path system of `K₂` (vertices `Bool`) in `path3`: `false ↦ 0`, `true ↦ 2`, with path
`0 → 1 → 2`. -/
def k2InPath3 : SubdivisionPaths (⊤ : SimpleGraph Bool) path3 where
  branch := ⟨fun b ↦ cond b 2 0, by decide⟩
  path
    | false, true, _ => walk012
    | true, false, _ => walk012.reverse
    | false, false, h => (h.ne rfl).elim
    | true, true, h => (h.ne rfl).elim
  isPath := by
    rintro (_ | _) (_ | _) h
    · exact (h.ne rfl).elim
    · show walk012.IsPath
      simp [walk012, Walk.cons_isPath_iff]
    · show walk012.reverse.IsPath
      exact (Walk.isPath_reverse_iff _).2 (by simp [walk012, Walk.cons_isPath_iff])
    · exact (h.ne rfl).elim
  path_symm := by
    rintro (_ | _) (_ | _) h
    · exact (h.ne rfl).elim
    · rfl
    · exact (Walk.reverse_reverse walk012).symm
    · exact (h.ne rfl).elim
  interior_not_branch := by
    rintro (_ | _) (_ | _) h x hx
    · exact (h.ne rfl).elim
    · change x ∈ walkInterior walk012 at hx
      rw [walkInterior_walk012, Set.mem_singleton_iff] at hx
      subst hx
      rintro ⟨(_ | _), hb⟩ <;> simp at hb
    · change x ∈ walkInterior walk012.reverse at hx
      rw [walkInterior_reverse, walkInterior_walk012, Set.mem_singleton_iff] at hx
      subst hx
      rintro ⟨(_ | _), hb⟩ <;> simp at hb
    · exact (h.ne rfl).elim
  disjoint := by
    rintro (_ | _) (_ | _) h (_ | _) (_ | _) h' hne
    all_goals first
      | exact (h.ne rfl).elim
      | exact (h'.ne rfl).elim
      | exact (hne (by simp)).elim

/-- The path of the positive example has nonempty interior. -/
theorem k2InPath3_interior :
    walkInterior (k2InPath3.path false true (by decide)) = {1} :=
  walkInterior_walk012

/-- For the same undirected edge, the path in the opposite direction is the reversed path and has
the same interior. -/
theorem k2InPath3_reverse :
    k2InPath3.path true false (by decide) = (k2InPath3.path false true (by decide)).reverse ∧
      walkInterior (k2InPath3.path true false (by decide)) = {1} :=
  ⟨k2InPath3.path_symm false true (by decide),
    (k2InPath3.walkInterior_path_symm (by decide)).trans walkInterior_walk012⟩

/-! ### Negative examples: candidate walks violate the fields -/

/-- The walk `1 → 0 → 2` in `star`. -/
def walk102 : star.Walk 1 2 :=
  .cons (show star.Adj 1 0 by decide) (.cons (show star.Adj 0 2 by decide) .nil)

/-- The walk `1 → 0 → 3` in `star`. -/
def walk103 : star.Walk 1 3 :=
  .cons (show star.Adj 1 0 by decide) (.cons (show star.Adj 0 3 by decide) .nil)

/-- The candidate walks `1 → 0 → 2` and `1 → 0 → 3` are paths. Still, they violate the
path-system conditions as shown below. -/
theorem walk102_isPath : walk102.IsPath := by simp [walk102, Walk.cons_isPath_iff]

theorem walk103_isPath : walk103.IsPath := by simp [walk103, Walk.cons_isPath_iff]

/-- The interior of the walk `1 → 0 → 2` contains the center `0`. -/
theorem zero_mem_walkInterior_walk102 : (0 : Fin 4) ∈ walkInterior walk102 := by
  simp only [mem_walkInterior, walk102, Walk.support_cons, Walk.support_nil]
  decide

/-- If the center `0` is a branch vertex, the walk `1 → 0 → 2` violates
`interior_not_branch`. -/
theorem walk102_violates_interior_not_branch {W : Type*} (f : W ↪ Fin 4)
    (h0 : (0 : Fin 4) ∈ Set.range f) : ¬ ∀ x ∈ walkInterior walk102, x ∉ Set.range f :=
  fun h ↦ h 0 zero_mem_walkInterior_walk102 h0

/-- The walks `1 → 0 → 2` and `1 → 0 → 3` share the interior vertex `0`, so using them as paths
of two distinct edges violates `disjoint`. -/
theorem walk102_walk103_not_disjoint :
    ¬ Disjoint (walkInterior walk102) (walkInterior walk103) := by
  intro h
  have h3 : (0 : Fin 4) ∈ walkInterior walk103 := by
    simp only [mem_walkInterior, walk103, Walk.support_cons, Walk.support_nil]
    decide
  exact Set.disjoint_left.1 h zero_mem_walkInterior_walk102 h3

end Kuratowski.PathsExamples
