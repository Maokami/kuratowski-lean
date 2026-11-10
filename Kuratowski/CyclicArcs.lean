import Kuratowski.CyclicWord

/-!
# Interiors of several arcs split by a cyclic order

Lemmas giving the interior-disjointness condition of path systems for cyclic orders of three and of
four points.
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

/-- Arcs over non-overlapping position intervals have disjoint interiors. -/
theorem disjoint_arc_interiors_of_le (C : CyclicSequence G m) (a b c d : ZMod m)
    (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) (hcd : c.val ≤ d.val) :
    Disjoint (walkInterior (C.arc a b)) (walkInterior (C.arc c d)) := by
  have : NeZero m := C.neZero
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, -, hi⟩ := (C.mem_support_arc a b x).mp hx.1
  rw [← hi, CyclicWord.mem_walkInterior_arc_iff, sbtw_iff_order] at hx hy
  omega

/-- An arc wrapping around the end of the circle and an interval inside its complement have
disjoint interiors. -/
theorem disjoint_arc_interiors_wrap (C : CyclicSequence G m) (a b c d : ZMod m)
    (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) (hcd : c.val ≤ d.val) :
    Disjoint (walkInterior (C.arc d a)) (walkInterior (C.arc b c)) := by
  have : NeZero m := C.neZero
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, -, hi⟩ := (C.mem_support_arc d a x).mp hx.1
  rw [← hi, CyclicWord.mem_walkInterior_arc_iff, sbtw_iff_order] at hx hy
  omega

/-- A vertex not on the cycle occurs in no arc. -/
theorem not_mem_arc_support_of_not_mem_range (C : CyclicSequence G m) {x : V}
    (hx : x ∉ Set.range C) (a b : ZMod m) : x ∉ (C.arc a b).support := by
  intro h
  obtain ⟨i, -, hi⟩ := (C.mem_support_arc a b x).mp h
  exact hx ⟨_, hi⟩

/-- A position outside a non-wrapping arc is not in its interior; this includes the
endpoints. -/
theorem not_mem_arc_interior_of_le (C : CyclicSequence G m) (a b t : ZMod m)
    (hab : a.val ≤ b.val) (ht : t.val ≤ a.val ∨ b.val ≤ t.val) :
    C t ∉ walkInterior (C.arc a b) := by
  have : NeZero m := C.neZero
  rw [CyclicWord.mem_walkInterior_arc_iff, sbtw_iff_order]
  omega

/-- The interior of an arc wrapping around the end of the circle avoids the middle closed
interval. -/
theorem not_mem_arc_interior_wrap (C : CyclicSequence G m) (a b t : ZMod m)
    (hat : a.val ≤ t.val) (htb : t.val ≤ b.val) :
    C t ∉ walkInterior (C.arc b a) := by
  have : NeZero m := C.neZero
  rw [CyclicWord.mem_walkInterior_arc_iff, sbtw_iff_order]
  omega

end Kuratowski.CyclicSequence
