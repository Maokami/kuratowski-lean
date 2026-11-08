import Kuratowski.Paths
import Kuratowski.ConnectedExamples

/-!
# 경로 체계의 예제

블루프린트 정의 `def:paths`의 작은 예. 그래프는 `ConnectedExamples`의 `path3`(경로 `0 - 1 - 2`)와
`star`(중심 `0`, 잎 `1, 2, 3`)를 쓴다.

* 양성 예: `K₂`(꼭짓점 `Bool`)를 `path3` 안에 `0 → 1 → 2`로 놓은 경로 체계. 경로의 내부는 `{1}`로
  비어 있지 않고, 반대 방향의 경로는 뒤집은 경로이며 내부가 같다.
* 음성 예(후보 걸음의 유한 사실): `star`의 경로 `1 → 0 → 2`는 내부에 `0`을 가진다. 그래서 `0`이
  분기점이면 `interior_not_branch`를 어긴다. 또 `1 → 0 → 2`와 `1 → 0 → 3`은 내부 `0`을 공유하므로,
  서로 다른 두 변의 경로로 쓰면 `disjoint`를 어긴다. 별 안에 `K₃`의 경로 체계가 전혀 없다는 일반적인
  주장은 여기서 증명하지 않는다.
-/

namespace Kuratowski.PathsExamples

open SimpleGraph Kuratowski.ConnectedExamples

/-! ### 양성 예 -/

/-- `path3`의 걸음 `0 → 1 → 2`. -/
def walk012 : path3.Walk 0 2 :=
  .cons (show path3.Adj 0 1 by decide) (.cons (show path3.Adj 1 2 by decide) .nil)

theorem walkInterior_walk012 : walkInterior walk012 = {1} := by
  ext x
  simp only [mem_walkInterior, walk012, Walk.support_cons, Walk.support_nil,
    Set.mem_singleton_iff]
  revert x
  decide

/-- `K₂`(꼭짓점 `Bool`)를 `path3` 안에 놓은 경로 체계: `false ↦ 0`, `true ↦ 2`, 경로 `0 → 1 → 2`. -/
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

/-- 양성 예의 경로는 내부가 비어 있지 않다. -/
theorem k2InPath3_interior :
    walkInterior (k2InPath3.path false true (by decide)) = {1} :=
  walkInterior_walk012

/-- 같은 무향 변의 반대 방향 경로는 뒤집은 경로이고 내부가 같다. -/
theorem k2InPath3_reverse :
    k2InPath3.path true false (by decide) = (k2InPath3.path false true (by decide)).reverse ∧
      walkInterior (k2InPath3.path true false (by decide)) = {1} :=
  ⟨k2InPath3.path_symm false true (by decide),
    (k2InPath3.walkInterior_path_symm (by decide)).trans walkInterior_walk012⟩

/-! ### 음성 예: 후보 걸음이 필드를 어긴다 -/

/-- `star`의 걸음 `1 → 0 → 2`. -/
def walk102 : star.Walk 1 2 :=
  .cons (show star.Adj 1 0 by decide) (.cons (show star.Adj 0 2 by decide) .nil)

/-- `star`의 걸음 `1 → 0 → 3`. -/
def walk103 : star.Walk 1 3 :=
  .cons (show star.Adj 1 0 by decide) (.cons (show star.Adj 0 3 by decide) .nil)

/-- 후보 걸음 `1 → 0 → 2`와 `1 → 0 → 3`은 실제로 경로다. 그래도 아래처럼 경로 체계의 조건을 어긴다. -/
theorem walk102_isPath : walk102.IsPath := by simp [walk102, Walk.cons_isPath_iff]

theorem walk103_isPath : walk103.IsPath := by simp [walk103, Walk.cons_isPath_iff]

/-- 걸음 `1 → 0 → 2`의 내부에는 중심 `0`이 있다. -/
theorem zero_mem_walkInterior_walk102 : (0 : Fin 4) ∈ walkInterior walk102 := by
  simp only [mem_walkInterior, walk102, Walk.support_cons, Walk.support_nil]
  decide

/-- 분기점에 중심 `0`이 들어 있으면, 걸음 `1 → 0 → 2`는 `interior_not_branch` 조건을 어긴다. -/
theorem walk102_violates_interior_not_branch {W : Type*} (f : W ↪ Fin 4)
    (h0 : (0 : Fin 4) ∈ Set.range f) : ¬ ∀ x ∈ walkInterior walk102, x ∉ Set.range f :=
  fun h ↦ h 0 zero_mem_walkInterior_walk102 h0

/-- 걸음 `1 → 0 → 2`와 `1 → 0 → 3`은 내부 `0`을 공유하므로, 서로 다른 두 변의 경로로 쓰면
`disjoint` 조건을 어긴다. -/
theorem walk102_walk103_not_disjoint :
    ¬ Disjoint (walkInterior walk102) (walkInterior walk103) := by
  intro h
  have h3 : (0 : Fin 4) ∈ walkInterior walk103 := by
    simp only [mem_walkInterior, walk103, Walk.support_cons, Walk.support_nil]
    decide
  exact Set.disjoint_left.1 h zero_mem_walkInterior_walk102 h3

end Kuratowski.PathsExamples
