import Kuratowski.Cyclic
import Kuratowski.Paths
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Cyclic vertex sequences and Mathlib cycle walks

We view the vertices of a `CyclicSequence` as an injective homomorphism from the standard cycle
graph and transport the standard cycle walk along it. The basic walk of the cycle graph runs in
the opposite direction, so we reverse it before transporting.
-/

namespace Kuratowski.CyclicSequence

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {n m : ℕ}

/-- The homomorphism sending the standard cycle graph to the given vertex sequence. Extra chords
are allowed. -/
def cycleGraphHom (C : CyclicSequence G (n + 3)) : cycleGraph (n + 3) →g G where
  toFun i := C (ZMod.finEquiv (n + 3) i)
  map_rel' := by
    intro u v h
    rcases cycleGraph_adj.mp h with h | h
    · have he : ZMod.finEquiv (n + 3) u = ZMod.finEquiv (n + 3) v + 1 := by
        apply sub_eq_iff_eq_add'.mp
        simpa using congrArg (ZMod.finEquiv (n + 3)) h
      change G.Adj (C (ZMod.finEquiv (n + 3) u)) (C (ZMod.finEquiv (n + 3) v))
      rw [he]
      exact (C.adj_next _).symm
    · have he : ZMod.finEquiv (n + 3) v = ZMod.finEquiv (n + 3) u + 1 := by
        apply sub_eq_iff_eq_add'.mp
        simpa using congrArg (ZMod.finEquiv (n + 3)) h
      change G.Adj (C (ZMod.finEquiv (n + 3) u)) (C (ZMod.finEquiv (n + 3) v))
      rw [he]
      exact C.adj_next _

theorem cycleGraphHom_injective (C : CyclicSequence G (n + 3)) :
    Function.Injective C.cycleGraphHom :=
  C.injective.comp (ZMod.finEquiv (n + 3)).injective

/-- The closed walk from position `0` back to itself, in the direction of the sequence. -/
def toWalk : {m : ℕ} → (C : CyclicSequence G m) → G.Walk (C 0) (C 0)
  | 0, C => False.elim (by have := C.length_ge_three; omega)
  | 1, C => False.elim (by have := C.length_ge_three; omega)
  | 2, C => False.elim (by have := C.length_ge_three; omega)
  | n + 3, C => ((cycleGraph.cycle n).reverse.map C.cycleGraphHom).copy
      (by simp [cycleGraphHom]) (by simp [cycleGraphHom])

theorem toWalk_isCycle (C : CyclicSequence G m) : C.toWalk.IsCycle := by
  match m with
  | 0 | 1 | 2 => have := C.length_ge_three; omega
  | n + 3 =>
    simp only [toWalk, Walk.isCycle_copy]
    exact cycleGraph.isCycle_cycle.reverse.map C.cycleGraphHom_injective

@[simp] theorem length_toWalk (C : CyclicSequence G m) : C.toWalk.length = m := by
  match m with
  | 0 | 1 | 2 => have := C.length_ge_three; omega
  | n + 3 => simp [toWalk]

theorem getVert_toWalk (C : CyclicSequence G m) (i : ℕ) (hi : i ≤ m) :
    C.toWalk.getVert i = C (i : ZMod m) := by
  match m with
  | 0 | 1 | 2 => have := C.length_ge_three; omega
  | n + 3 =>
    simp only [toWalk, Walk.getVert_copy, Walk.getVert_map, Walk.getVert_reverse,
      cycleGraph.length_cycle]
    rw [cycleGraph.getVert_cycle (by omega)]
    change C (ZMod.finEquiv (n + 3) _) = C _
    congr 1
    apply ZMod.val_injective (n + 3)
    simp [ZMod.finEquiv, Nat.sub_sub_self hi]
    rfl

/-- The arc from `a` forward to the first visit of `b`. It has length 0 when `a = b`. -/
def arc (C : CyclicSequence G m) (a b : ZMod m) : G.Walk (C a) (C b) := by
  letI : NeZero m := C.neZero
  exact ((C.rotate a).toWalk.take (b - a).val).copy
    (by simp)
    (by
      rw [getVert_toWalk _ _ (Nat.le_of_lt (ZMod.val_lt _))]
      simp)

theorem arc_isPath (C : CyclicSequence G m) (a b : ZMod m) : (C.arc a b).IsPath := by
  have : NeZero m := C.neZero
  simp only [arc, Walk.isPath_copy]
  exact (C.rotate a).toWalk_isCycle.isPath_take (by
    rw [length_toWalk]
    exact ZMod.val_lt _)

@[simp] theorem length_arc (C : CyclicSequence G m) (a b : ZMod m) :
    (C.arc a b).length = (b - a).val := by
  have : NeZero m := C.neZero
  simp only [arc, Walk.length_copy, Walk.take_length, length_toWalk]
  exact Nat.min_eq_left (Nat.le_of_lt (ZMod.val_lt _))

theorem getVert_arc (C : CyclicSequence G m) (a b : ZMod m) (i : ℕ)
    (hi : i ≤ (b - a).val) : (C.arc a b).getVert i = C ((i : ZMod m) + a) := by
  have : NeZero m := C.neZero
  simp only [arc, Walk.getVert_copy, Walk.take_getVert]
  rw [Nat.min_eq_right hi, getVert_toWalk _ _ (by have := ZMod.val_lt (b - a); omega)]
  simp

theorem mem_support_arc (C : CyclicSequence G m) (a b : ZMod m) (v : V) :
    v ∈ (C.arc a b).support ↔ ∃ i ≤ (b - a).val, C ((i : ZMod m) + a) = v := by
  rw [Walk.mem_support_iff_exists_getVert]
  constructor
  · rintro ⟨i, hv, hi⟩
    rw [length_arc] at hi
    exact ⟨i, hi, by simpa [getVert_arc C a b i hi] using hv⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨i, by simpa [getVert_arc C a b i hi] using hv, by simpa using hi⟩

theorem mem_support_arc_iff (C : CyclicSequence G m) (a b t : ZMod m) :
    C t ∈ (C.arc a b).support ↔ (t - a).val ≤ (b - a).val := by
  have : NeZero m := C.neZero
  rw [mem_support_arc]
  constructor
  · rintro ⟨i, hi, ht⟩
    have he : (i : ZMod m) = t - a := eq_sub_iff_add_eq.mpr (C.injective ht)
    have hlt : i < m := lt_of_le_of_lt hi (ZMod.val_lt _)
    have hv : i = (t - a).val := by
      simpa [ZMod.val_natCast_of_lt hlt] using congrArg ZMod.val he
    omega
  · intro h
    exact ⟨(t - a).val, h, by simp⟩

theorem mem_walkInterior_arc (C : CyclicSequence G m) (a b t : ZMod m) :
    C t ∈ walkInterior (C.arc a b) ↔
      0 < (t - a).val ∧ (t - a).val < (b - a).val := by
  have : NeZero m := C.neZero
  have hz : (t - a).val = 0 ↔ t = a := by rw [ZMod.val_eq_zero, sub_eq_zero]
  have hd : (t - a).val = (b - a).val ↔ t = b := by
    rw [(ZMod.val_injective m).eq_iff, sub_left_inj]
  rw [mem_walkInterior, mem_support_arc_iff]
  simp only [ne_eq, apply_eq_iff]
  constructor
  · rintro ⟨h, ha, hb⟩
    have hzero := mt hz.mp ha
    have hdiff := mt hd.mp hb
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨by omega, ?_, ?_⟩
    · intro h
      have := hz.mpr h
      omega
    · intro h
      have := hd.mpr h
      omega

private theorem not_in_both_open_arcs [NeZero m] (a b t : ZMod m) :
    ¬ ((t - a).val < (b - a).val ∧ (t - b).val < (a - b).val) := by
  rintro ⟨ha, hb⟩
  by_cases hab : a = b
  · subst b
    simp at ha
  have hpos : 0 < (b - a).val := by
    have hn := (ZMod.val_eq_zero (b - a)).not.mpr (sub_ne_zero.mpr (Ne.symm hab))
    omega
  have hcancel : (b - a) + (a - b) = 0 := by simp
  have hsum : m ≤ (b - a).val + (a - b).val := by
    by_contra h
    have hh := ZMod.val_add_of_lt (by omega : (b - a).val + (a - b).val < m)
    rw [hcancel] at hh
    simp only [ZMod.val_zero] at hh
    omega
  have htotal := ZMod.val_add_val_of_le hsum
  rw [hcancel] at htotal
  simp only [ZMod.val_zero, zero_add] at htotal
  have htranslate : (t - b) + (b - a) = t - a := by simp
  have hcross : m ≤ (t - b).val + (b - a).val := by
    by_contra h
    have hh := ZMod.val_add_of_lt (by omega : (t - b).val + (b - a).val < m)
    rw [htranslate] at hh
    omega
  omega

/-- The two arcs in opposite directions meet only at their endpoints. -/
theorem disjoint_arc_interiors (C : CyclicSequence G m) (a b : ZMod m) :
    Disjoint (walkInterior (C.arc a b)) (walkInterior (C.arc b a)) := by
  have : NeZero m := C.neZero
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, hi, hlabel⟩ := (C.mem_support_arc a b x).mp hx.1
  rw [← hlabel, mem_walkInterior_arc] at hx hy
  exact not_in_both_open_arcs a b _ ⟨hx.2, hy.2⟩

end Kuratowski.CyclicSequence
