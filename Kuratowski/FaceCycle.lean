import Kuratowski.Cyclic
import Kuratowski.FaceBoundary

/-!
# 면 순환을 순환 꼭짓점 수열로 (블루프린트 `lem:J2`의 준비)

2-연결 그래프의 종수 0 회전 체계에서 다트 `d`의 면은 순환 꼭짓점 수열이다
(`RotationSystem.exists_cyclicSequence_face`). 길이는 `d`의 면 순열 최소 주기이고, `k`번째 점은
`φ^k d`의 시작점이다. 그래서 시작점과 진행 방향이 보존된다.

* 꼭짓점이 겹치지 않는 것은 보조정리 `lem:J1`(`eq_of_sameCycle_facePerm_of_fst_eq`)에서 온다.
* 길이가 1이면 `φ d = d`라 `d`가 고리가 되고, 길이가 2이면 `φ d = d.symm`이라 `d`의 두 끝이 모두
  차수 1이 되어 2-연결성에 어긋난다. 길이 3 이상에는 종수 0이 필요 없다.
-/

namespace Kuratowski

open SimpleGraph Equiv Equiv.Perm Function

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

variable [Finite V] [DecidableEq V] (R : RotationSystem G)

/-- 다트 `d`의 면의 길이: 면 순열의 최소 주기. -/
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
/-- 길이가 1인 면은 없다: `φ d = d`이면 `d`의 두 끝이 같아진다. -/
theorem faceLength_ne_one (d : G.Dart) : R.faceLength d ≠ 1 := by
  intro h
  have h1 := R.facePerm_pow_faceLength d
  rw [h, pow_one] at h1
  have := R.facePerm_fst d
  rw [h1] at this
  exact d.adj.ne this

omit [DecidableEq V] in
/-- `ρ d = d`이면 `d`의 시작점의 이웃은 `d`의 끝점뿐이다. -/
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
/-- 2-연결이면 길이가 2인 면은 없다. 그런 면에서는 `φ d = d.symm`, `φ d.symm = d`라
`d`의 두 끝이 모두 차수 1이 된다. -/
theorem faceLength_ne_two (hG : TwoConnected G) (d : G.Dart) : R.faceLength d ≠ 2 := by
  intro h
  have h2 := R.facePerm_pow_faceLength d
  rw [h, pow_two, Perm.mul_apply] at h2
  set e := R.facePerm d with he
  have he1 : e.fst = d.snd := R.facePerm_fst d
  have he2 : e.snd = d.fst := by rw [← R.facePerm_fst e, h2]
  have hes : e = d.symm := Dart.ext _ _ (Prod.ext he1 he2)
  -- `ρ d = d`: `φ d.symm = d`이고 `φ d.symm = ρ d`
  have hrot : R.rot d = d := by
    have : R.facePerm d.symm = d := by rw [← hes]; exact h2
    rwa [facePerm_apply, Dart.symm_symm] at this
  -- 지지점이 3개 이상이므로 `d`의 두 끝이 아닌 지지점 `z`가 있다
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

/-- 2-연결 그래프의 종수 0 회전 체계에서 다트 `d`의 면은 순환 꼭짓점 수열이다. `k`번째 점은
`φ^k d`의 시작점이다. -/
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
