import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Cyclic vertex sequences

A `CyclicSequence G m` is an injective map `ZMod m → V`, with `3 ≤ m`, whose
consecutive vertices are adjacent. Modular indexing includes the closing edge.
Cycles need not be induced. `rotate`, `reverse`, and `mono` change the starting
point, orientation, and ambient graph. `CyclicWalk` constructs walks and arcs.
Blueprint: `def:cycseq`.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {m : ℕ}

/-- An injective cyclic vertex sequence of length at least three. -/
structure CyclicSequence (G : SimpleGraph V) (m : ℕ) where
  length_ge_three : 3 ≤ m
  vertex : ZMod m ↪ V
  adj_next : ∀ i, G.Adj (vertex i) (vertex (i + 1))

namespace CyclicSequence

instance : CoeFun (CyclicSequence G m) (fun _ ↦ ZMod m → V) := ⟨fun C ↦ C.vertex⟩

theorem injective (C : CyclicSequence G m) : Function.Injective C := C.vertex.injective

@[simp] theorem apply_eq_iff (C : CyclicSequence G m) (i j : ZMod m) : C i = C j ↔ i = j :=
  C.injective.eq_iff

theorem length_pos (C : CyclicSequence G m) : 0 < m := by
  have := C.length_ge_three
  omega

/-- The positive length supplies `NeZero m` when finite `ZMod m` instances are needed. -/
theorem neZero (C : CyclicSequence G m) : NeZero m := ⟨Nat.ne_of_gt C.length_pos⟩

@[ext] theorem ext {C D : CyclicSequence G m} (h : ∀ i, C i = D i) : C = D := by
  have hvertex : C.vertex = D.vertex := Function.Embedding.ext h
  cases C
  cases D
  cases hvertex
  rfl

theorem ne_next (C : CyclicSequence G m) (i : ZMod m) : C i ≠ C (i + 1) :=
  (C.adj_next i).ne

/-- The cyclic adjacency condition includes the closing edge from `-1` to `0`. -/
theorem adj_last_zero (C : CyclicSequence G m) : G.Adj (C (-1)) (C 0) := by
  simpa using C.adj_next (-1)

/-- Shift the starting index by `a`. -/
def rotate (C : CyclicSequence G m) (a : ZMod m) : CyclicSequence G m where
  length_ge_three := C.length_ge_three
  vertex := ⟨fun i ↦ C (i + a), fun _ _ h ↦ add_right_cancel (C.injective h)⟩
  adj_next i := by simpa [add_assoc, add_comm, add_left_comm] using C.adj_next (i + a)

@[simp] theorem rotate_apply (C : CyclicSequence G m) (a i : ZMod m) :
    C.rotate a i = C (i + a) := rfl

/-- Reverse the orientation while fixing index `0`. -/
def reverse (C : CyclicSequence G m) : CyclicSequence G m where
  length_ge_three := C.length_ge_three
  vertex := ⟨fun i ↦ C (-i), fun _ _ h ↦ neg_injective (C.injective h)⟩
  adj_next i := by
    change G.Adj (C (-i)) (C (-(i + 1)))
    simpa using (C.adj_next (-(i + 1))).symm

@[simp] theorem reverse_apply (C : CyclicSequence G m) (i : ZMod m) :
    C.reverse i = C (-i) := rfl

@[simp] theorem rotate_zero (C : CyclicSequence G m) : C.rotate 0 = C := by
  ext i
  simp

@[simp] theorem reverse_reverse (C : CyclicSequence G m) : C.reverse.reverse = C := by
  ext i
  simp

/-- Lengths zero, one, and two are excluded. -/
theorem not_nonempty_of_lt_three (h : m < 3) : ¬ Nonempty (CyclicSequence G m) := by
  rintro ⟨C⟩
  have := C.length_ge_three
  omega

/-- An edgeless graph has no cyclic vertex sequence. -/
theorem not_nonempty_bot : ¬ Nonempty (CyclicSequence (⊥ : SimpleGraph V) m) := by
  rintro ⟨C⟩
  exact C.adj_next 0

/-- The triangle `0 → 1 → 2 → 0`. -/
def triangle : CyclicSequence (⊤ : SimpleGraph (ZMod 3)) 3 where
  length_ge_three := by decide
  vertex := Function.Embedding.refl _
  adj_next := by decide +kernel

/-- Check cyclic closure using `2 + 1 = 0` in `ZMod 3` and `adj_next`. -/
theorem triangle_closing_edge :
    (⊤ : SimpleGraph (ZMod 3)).Adj (triangle 2) (triangle 0) := by
  have hwrap : (2 : ZMod 3) + 1 = 0 := by decide
  simpa only [hwrap] using triangle.adj_next (2 : ZMod 3)

end CyclicSequence

namespace CyclicSequence

/-- View a cyclic sequence in a subgraph as one in the ambient graph. -/
def mono {G H : SimpleGraph V} {m : ℕ} (C : CyclicSequence H m) (hle : H ≤ G) :
    CyclicSequence G m where
  length_ge_three := C.length_ge_three
  vertex := C.vertex
  adj_next i := hle (C.adj_next i)

@[simp] theorem mono_apply {G H : SimpleGraph V} {m : ℕ}
    (C : CyclicSequence H m) (hle : H ≤ G) (i : ZMod m) :
    C.mono hle i = C i := rfl

end CyclicSequence

end Kuratowski
