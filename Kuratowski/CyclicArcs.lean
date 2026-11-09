import Kuratowski.CyclicWord

/-!
# 순환 순서로 나눈 여러 호의 내부

세 점과 네 점의 순환 순서에서 경로 체계의 내부 서로소 조건을 얻기 위한 보조정리.
-/

namespace Kuratowski.CyclicSequence

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {m : ℕ}

private theorem sbtw_iff_order [NeZero m] (a t b : ZMod m) :
    sbtw a t b ↔ a.val < t.val ∧ t.val < b.val ∨
      t.val < b.val ∧ b.val < a.val ∨ b.val < a.val ∧ a.val < t.val := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- 서로 겹치지 않는 위치 구간에 대응하는 두 호의 내부는 서로소다. -/
theorem disjoint_arc_interiors_of_le (C : CyclicSequence G m) (a b c d : ZMod m)
    (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) (hcd : c.val ≤ d.val) :
    Disjoint (walkInterior (C.arc a b)) (walkInterior (C.arc c d)) := by
  have : NeZero m := C.neZero
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, -, hi⟩ := (C.mem_support_arc a b x).mp hx.1
  rw [← hi, CyclicWord.mem_walkInterior_arc_iff, sbtw_iff_order] at hx hy
  omega

/-- 원의 끝을 넘어가는 호와 그 여집합 안의 한 구간은 내부에서 만나지 않는다. -/
theorem disjoint_arc_interiors_wrap (C : CyclicSequence G m) (a b c d : ZMod m)
    (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) (hcd : c.val ≤ d.val) :
    Disjoint (walkInterior (C.arc d a)) (walkInterior (C.arc b c)) := by
  have : NeZero m := C.neZero
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, -, hi⟩ := (C.mem_support_arc d a x).mp hx.1
  rw [← hi, CyclicWord.mem_walkInterior_arc_iff, sbtw_iff_order] at hx hy
  omega

/-- 사이클 위에 없는 꼭짓점은 어느 호에도 나타나지 않는다. -/
theorem not_mem_arc_support_of_not_mem_range (C : CyclicSequence G m) {x : V}
    (hx : x ∉ Set.range C) (a b : ZMod m) : x ∉ (C.arc a b).support := by
  intro h
  obtain ⟨i, -, hi⟩ := (C.mem_support_arc a b x).mp h
  exact hx ⟨_, hi⟩

/-- 감기지 않는 호의 바깥 위치는 그 내부에 없다. 끝점도 포함한다. -/
theorem not_mem_arc_interior_of_le (C : CyclicSequence G m) (a b t : ZMod m)
    (hab : a.val ≤ b.val) (ht : t.val ≤ a.val ∨ b.val ≤ t.val) :
    C t ∉ walkInterior (C.arc a b) := by
  have : NeZero m := C.neZero
  rw [CyclicWord.mem_walkInterior_arc_iff, sbtw_iff_order]
  omega

/-- 원의 끝을 넘어가는 호의 내부는 가운데 닫힌 구간을 피한다. -/
theorem not_mem_arc_interior_wrap (C : CyclicSequence G m) (a b t : ZMod m)
    (hat : a.val ≤ t.val) (htb : t.val ≤ b.val) :
    C t ∉ walkInterior (C.arc b a) := by
  have : NeZero m := C.neZero
  rw [CyclicWord.mem_walkInterior_arc_iff, sbtw_iff_order]
  omega

end Kuratowski.CyclicSequence
