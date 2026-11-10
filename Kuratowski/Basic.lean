import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Kuratowski.Perm

/-!
# Combinatorial planarity: rotation systems and Euler characteristic

A rotation system gives a cyclic order on the outgoing darts at each vertex.
It is represented by a permutation `rot` that preserves the initial vertex and
has a single orbit on its outgoing darts. The face permutation is
`φ d = rot d.symm`: traverse `d`, then take the next dart after its reverse.

We use the combinatorial definition of planarity from topological graph theory
(Mohar–Thomassen, *Graphs on Surfaces*, Chapter 3). For a finite connected graph,
a rotation system describes an orientable cellular embedding, with
`|V| - |E| + |F| = 2 - 2g`. This topological correspondence is background motivation;
it is not formalized in this library.

For disconnected graphs, each isolated vertex contributes one face. Planarity
means `|V| - |E| + |F| = 2 * |ConnectedComponent|`. The Euler inequality proved in
`Kuratowski.Euler` bounds the left side by the right side for every rotation system.

Counts use `Nat.card` and `Set.ncard`, so the definitions do not depend on chosen
`Fintype` or decidable-adjacency instances. Finiteness is assumed in the counting theorems.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*}

/-- A finite vertex type gives a finite dart type. -/
instance {G : SimpleGraph V} [Finite V] : Finite G.Dart :=
  Finite.of_injective _ SimpleGraph.Dart.toProd_injective

/-- A rotation system on `G`. -/
structure RotationSystem (G : SimpleGraph V) where
  /-- Cyclic orders on the outgoing darts. -/
  rot : Equiv.Perm G.Dart
  /-- Rotation preserves the initial vertex. -/
  fst_rot : ∀ d, (rot d).fst = d.fst
  /-- All darts with the same initial vertex lie in one rotation cycle. -/
  sameCycle_rot : ∀ d d' : G.Dart, d.fst = d'.fst → rot.SameCycle d d'

namespace RotationSystem

variable {G : SimpleGraph V} (R : RotationSystem G)

/-- The face permutation `φ d = rot d.symm`. -/
def facePerm : Equiv.Perm G.Dart :=
  (Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive).trans R.rot

@[simp] lemma facePerm_apply (d : G.Dart) : R.facePerm d = R.rot d.symm := rfl

/-- A face-permutation orbit; isolated-vertex faces are counted separately. -/
abbrev Face := Quotient (Equiv.Perm.SameCycle.setoid R.facePerm)

lemma card_face : Nat.card R.Face = orbitCount R.facePerm := rfl

/-- The number of face-permutation orbits plus the number of isolated vertices. -/
noncomputable def numFaces : ℕ := orbitCount R.facePerm + {v | G.IsIsolated v}.ncard

/-- The Euler characteristic `|V| - |E| + |F|`. -/
noncomputable def eulerChar : ℤ := Nat.card V - G.edgeSet.ncard + R.numFaces

end RotationSystem

/-- Combinatorial planarity: some rotation system has Euler characteristic
`2 * |ConnectedComponent|`. For a finite connected graph, this is the genus-zero equation. -/
def IsPlanar (G : SimpleGraph V) : Prop :=
  ∃ R : RotationSystem G, R.eulerChar = 2 * Nat.card G.ConnectedComponent

/-! ## Counting darts and edges -/

lemma card_dart_eq [Finite V] (G : SimpleGraph V) : Nat.card G.Dart = 2 * G.edgeSet.ncard := by
  classical
  have := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, G.dart_card_eq_twice_card_edges, ← coe_edgeFinset,
    Set.ncard_coe_finset]

/-! ## Basic properties of the face permutation -/

namespace RotationSystem

variable {G : SimpleGraph V} (R : RotationSystem G)

/-- If rotation fixes `d`, it is the only outgoing dart at its initial vertex. -/
lemma eq_of_rot_eq_self {d : G.Dart} (h : R.rot d = d) {d' : G.Dart} (h' : d'.fst = d.fst) :
    d' = d := by
  obtain ⟨i, hi⟩ := R.sameCycle_rot d d' h'.symm
  rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h i] at hi
  exact hi.symm

/-- Another neighbor of `d.fst` prevents `d` from being fixed by rotation. -/
lemma rot_ne_self {d : G.Dart} {w : V} (hw : G.Adj d.fst w) (hne : w ≠ d.snd) :
    R.rot d ≠ d := fun h =>
  hne (congrArg (fun x : G.Dart => x.snd) (R.eq_of_rot_eq_self h (d' := ⟨(d.fst, w), hw⟩) rfl))

@[simp] lemma facePerm_fst (d : G.Dart) : (R.facePerm d).fst = d.snd := by
  simp [R.fst_rot]

/-- A loopless graph has no face-permutation fixed point. -/
lemma facePerm_ne_self (d : G.Dart) : R.facePerm d ≠ d := by
  intro h
  have := congrArg (fun x : G.Dart => x.fst) h
  simp only [facePerm_fst] at this
  exact d.snd_ne_fst this

/-- If `d.snd` has a neighbor other than `d.fst`, then `φ (φ d) ≠ d`.
A face of length two can occur only at an endpoint of degree one. -/
lemma facePerm_facePerm_ne_self (d : G.Dart) {z : V} (hz : G.Adj d.snd z) (hne : z ≠ d.fst) :
    R.facePerm (R.facePerm d) ≠ d := by
  intro h
  have h1 : (R.facePerm d).snd = d.fst := by
    have := congrArg (fun x : G.Dart => x.fst) h
    simpa only [facePerm_fst] using this
  have hx : R.facePerm d = d.symm := by
    ext
    · simp [R.fst_rot]
    · simpa using h1
  exact R.rot_ne_self (d := d.symm) hz hne hx

end RotationSystem

/-! ## Bounding the number of orbits -/

/-- If every orbit has at least `m` elements, then `m * orbitCount f ≤ Nat.card α`. -/
lemma mul_orbitCount_le {α : Type*} [Finite α] (f : Equiv.Perm α) (m : ℕ)
    (h : ∀ x k, 0 < k → k < m → (f ^ k) x ≠ x) :
    m * orbitCount f ≤ Nat.card α := by
  classical
  have := Fintype.ofFinite α
  set q : α → Quotient (Equiv.Perm.SameCycle.setoid f) := Quotient.mk _
  unfold orbitCount
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Finset.card_univ (α := α),
    Finset.card_eq_sum_card_fiberwise (f := q) (t := Finset.univ) (fun _ _ => Finset.mem_univ _),
    mul_comm, ← smul_eq_mul, ← Finset.card_univ]
  refine Finset.card_nsmul_le_sum _ _ _ fun c _ => ?_
  set x := c.out
  have key : ∀ i j, i < j → j < m → (f ^ i) x ≠ (f ^ j) x := by
    intro i j hij hj heq
    apply h ((f ^ i) x) (j - i) (Nat.sub_pos_of_lt hij) (by omega)
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hij.le]
    exact heq.symm
  calc m = (Finset.range m).card := (Finset.card_range m).symm
    _ ≤ (Finset.univ.filter fun a => q a = c).card := by
      refine Finset.card_le_card_of_injOn (fun i => (f ^ i) x) ?_ ?_
      · intro i _
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        rw [← Quotient.out_eq c]
        exact Quotient.sound (Equiv.Perm.sameCycle_pow_left.2 (Equiv.Perm.SameCycle.refl f x))
      · intro i hi j hj hij
        simp only [Finset.coe_range, Set.mem_Iio] at hi hj
        rcases lt_trichotomy i j with hlt | heq | hgt
        · exact absurd hij (key i j hlt hj)
        · exact heq
        · exact absurd hij.symm (key j i hgt hi)

end Kuratowski
