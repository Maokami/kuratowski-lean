import Kuratowski.Cyclic
import Kuratowski.FaceBoundary

/-!
# Face cycles as cyclic vertex sequences (preparation for blueprint `lem:J2`)

For a genus-0 rotation system of a 2-connected graph, the face of a dart `d` is a cyclic vertex
sequence (`RotationSystem.exists_cyclicSequence_face`). Its length is the minimal period of `d`
under the face permutation, and its `k`-th vertex is the start vertex of `φ^k d`. Hence the
starting point and the direction are preserved.

* The vertices are distinct by lemma `lem:J1` (`eq_of_sameCycle_facePerm_of_fst_eq`).
* Length 1 would give `φ d = d`, making `d` a loop. Length 2 would give `φ d = d.symm`, so both
  ends of `d` would have degree 1, contradicting 2-connectivity. The bound `length ≥ 3` does not
  need genus 0.
-/

namespace Kuratowski

open SimpleGraph Equiv Equiv.Perm Function

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

variable [Finite V] [DecidableEq V] (R : RotationSystem G)

/-- The length of the face of a dart `d`: the minimal period of the face permutation. -/
noncomputable def faceLength (d : G.Dart) : ℕ := minimalPeriod R.facePerm d

omit [DecidableEq V] in
theorem faceLength_pos (d : G.Dart) : 0 < R.faceLength d :=
  IsPeriodicPt.minimalPeriod_pos (orderOf_pos R.facePerm) (by
    change (⇑R.facePerm)^[orderOf R.facePerm] d = d
    rw [← coe_pow, pow_orderOf_eq_one]
    rfl)

omit [Finite V] [DecidableEq V] in
theorem facePerm_pow_mod (d : G.Dart) (k : ℕ) :
    (R.facePerm ^ (k % R.faceLength d)) d = (R.facePerm ^ k) d := by
  rw [coe_pow, coe_pow]
  exact iterate_mod_minimalPeriod_eq

omit [Finite V] [DecidableEq V] in
theorem facePerm_pow_faceLength (d : G.Dart) : (R.facePerm ^ R.faceLength d) d = d := by
  rw [coe_pow]
  exact iterate_minimalPeriod

omit [Finite V] [DecidableEq V] in
theorem eq_of_facePerm_pow_eq {d : G.Dart} {a b : ℕ} (ha : a < R.faceLength d)
    (hb : b < R.faceLength d) (h : (R.facePerm ^ a) d = (R.facePerm ^ b) d) : a = b :=
  iterate_injOn_Iio_minimalPeriod ha hb (by simpa only [coe_pow] using h)

omit [Finite V] [DecidableEq V] in
/-- No face has length 1: `φ d = d` would make the two ends of `d` equal. -/
theorem faceLength_ne_one (d : G.Dart) : R.faceLength d ≠ 1 := by
  intro h
  have h1 := R.facePerm_pow_faceLength d
  rw [h, pow_one] at h1
  have := R.facePerm_fst d
  rw [h1] at this
  exact d.adj.ne this

omit [DecidableEq V] in
/-- If `ρ d = d`, the only neighbor of the start vertex of `d` is the end vertex of `d`. -/
theorem adj_eq_of_rot_eq (d : G.Dart) (hd : R.rot d = d) {z : V} (hz : G.Adj d.fst z) :
    z = d.snd := by
  let e : G.Dart := ⟨(d.fst, z), hz⟩
  obtain ⟨n, hn⟩ := (R.sameCycle_rot d e rfl).exists_nat_pow_eq
  have hpow : ∀ n : ℕ, (R.rot ^ n) d = d := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Perm.mul_apply, ih, hd]
  rw [hpow] at hn
  exact (congrArg Prod.snd (congrArg Dart.toProd hn)).symm

omit [DecidableEq V] in
/-- A 2-connected graph has no face of length 2. On such a face `φ d = d.symm` and
`φ d.symm = d`, so both ends of `d` have degree 1. -/
theorem faceLength_ne_two (hG : TwoConnected G) (d : G.Dart) : R.faceLength d ≠ 2 := by
  intro h
  have h2 := R.facePerm_pow_faceLength d
  rw [h, pow_two, Perm.mul_apply] at h2
  set e := R.facePerm d with he
  have he1 : e.fst = d.snd := R.facePerm_fst d
  have he2 : e.snd = d.fst := by rw [← R.facePerm_fst e, h2]
  have hes : e = d.symm := Dart.ext _ _ (Prod.ext he1 he2)
  -- `ρ d = d`: `φ d.symm = d` and `φ d.symm = ρ d`
  have hrot : R.rot d = d := by
    have : R.facePerm d.symm = d := by rw [← hes]; exact h2
    rwa [facePerm_apply, Dart.symm_symm] at this
  -- the support has at least 3 vertices, so some support vertex `z` is not an end of `d`
  have hpair : ({d.fst, d.snd} : Set V).ncard < G.support.ncard := by
    have := hG.1
    rw [Set.ncard_pair d.adj.ne]
    omega
  obtain ⟨z, hz, hzn⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hpair
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hzn
  refine not_connectedOn_of_isolated G 2 G.support {d.snd} (by simp) (u := d.fst) (v := z)
    ⟨d.adj.mem_support_left, fun h' ↦ d.adj.ne (Set.mem_singleton_iff.1 h')⟩
    ⟨hz, fun h' ↦ hzn.2 (Set.mem_singleton_iff.1 h')⟩ (fun h' ↦ hzn.1 h'.symm) ?_ hG
  rintro t ⟨ht, -, htv⟩
  exact htv (Set.mem_singleton_iff.2 (R.adj_eq_of_rot_eq d hrot ht))

omit [DecidableEq V] in
theorem three_le_faceLength (hG : TwoConnected G) (d : G.Dart) : 3 ≤ R.faceLength d := by
  have h0 := R.faceLength_pos d
  have h1 := R.faceLength_ne_one d
  have h2 := R.faceLength_ne_two hG d
  omega

/-- For a genus-0 rotation system of a 2-connected graph, the face of a dart `d` is a cyclic
vertex sequence whose `k`-th vertex is the start vertex of `φ^k d`. -/
theorem exists_cyclicSequence_face (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d : G.Dart) :
    ∃ m, ∃ C : CyclicSequence G m, ∀ k : ℕ, C (k : ZMod m) = ((R.facePerm ^ k) d).fst := by
  set m := R.faceLength d with hmdef
  have hm3 : 3 ≤ m := R.three_le_faceLength hG d
  have : NeZero m := ⟨by omega⟩
  let f : ZMod m → V := fun i ↦ ((R.facePerm ^ i.val) d).fst
  have hf : ∀ k : ℕ, f (k : ZMod m) = ((R.facePerm ^ k) d).fst := by
    intro k
    simp only [f, ZMod.val_natCast]
    rw [R.facePerm_pow_mod d k]
  have hinj : Function.Injective f := by
    intro i j hij
    have hsame : R.facePerm.SameCycle ((R.facePerm ^ i.val) d) ((R.facePerm ^ j.val) d) :=
      (SameCycle.refl _ d |>.trans ⟨i.val, rfl⟩).symm.trans ⟨j.val, rfl⟩
    have heq := R.eq_of_sameCycle_facePerm_of_fst_eq hG hR hsame hij
    exact ZMod.val_injective m (R.eq_of_facePerm_pow_eq (ZMod.val_lt i) (ZMod.val_lt j) heq)
  refine ⟨m, ⟨hm3, ⟨f, hinj⟩, fun i ↦ ?_⟩, hf⟩
  change G.Adj (f i) (f (i + 1))
  have hi : i = ((i.val : ℕ) : ZMod m) := (ZMod.natCast_zmod_val i).symm
  have hi1 : i + 1 = ((i.val + 1 : ℕ) : ZMod m) := by
    rw [Nat.cast_add, Nat.cast_one, ← hi]
  rw [hi1, hf, hi, hf, pow_succ', Perm.mul_apply, ← hi]
  rw [R.facePerm_fst]
  exact ((R.facePerm ^ i.val) d).adj

end RotationSystem

end Kuratowski
