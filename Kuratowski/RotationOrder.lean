import Kuratowski.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Rotation periods and neighbor enumeration

For a dart `d` of a finite graph, the inverse rotation has period `|N(d.fst)|`.
The endpoints of `(R.rot⁻¹ ^ j) d`, for `0 ≤ j < |N(d.fst)|`, enumerate the
neighbors exactly once. The same enumeration is expressed using `ZMod` indices.
-/

namespace Kuratowski

open SimpleGraph Equiv Equiv.Perm Function

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

variable (R : RotationSystem G)

/-! ### Inverse rotation: period and neighbor enumeration -/

/-- Inverse rotation preserves the initial vertex. -/
theorem fst_rot_inv (d : G.Dart) : (R.rot⁻¹ d).fst = d.fst := by
  simpa using (R.fst_rot (R.rot⁻¹ d)).symm

theorem fst_rot_inv_pow (d : G.Dart) (j : ℕ) : ((R.rot⁻¹ ^ j) d).fst = d.fst := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', Perm.mul_apply, fst_rot_inv, ih]

variable [Finite V]

theorem minimalPeriod_rot_inv_pos (d : G.Dart) : 0 < minimalPeriod ⇑(R.rot⁻¹) d :=
  IsPeriodicPt.minimalPeriod_pos (orderOf_pos R.rot⁻¹) (by
    change (⇑R.rot⁻¹)^[orderOf R.rot⁻¹] d = d
    rw [← coe_pow, pow_orderOf_eq_one]
    rfl)

omit [Finite V] in
/-- Endpoints of `ρ⁻¹^j d` are distinct for indices below the minimal period. -/
theorem eq_of_rot_inv_pow_snd_eq (d : G.Dart) {i j : ℕ} (hi : i < minimalPeriod ⇑(R.rot⁻¹) d)
    (hj : j < minimalPeriod ⇑(R.rot⁻¹) d) (h : ((R.rot⁻¹ ^ i) d).snd = ((R.rot⁻¹ ^ j) d).snd) :
    i = j := by
  have hd : (R.rot⁻¹ ^ i) d = (R.rot⁻¹ ^ j) d :=
    Dart.ext _ _ (Prod.ext (by rw [R.fst_rot_inv_pow, R.fst_rot_inv_pow]) h)
  exact iterate_injOn_Iio_minimalPeriod hi hj (by simpa only [coe_pow] using hd)

/-- Each neighbor of `d.fst` occurs as `(ρ⁻¹^j d).snd` below the minimal period. -/
theorem exists_rot_inv_pow_snd (d : G.Dart) {w : V} (hw : G.Adj d.fst w) :
    ∃ j < minimalPeriod ⇑(R.rot⁻¹) d, ((R.rot⁻¹ ^ j) d).snd = w := by
  let y : G.Dart := ⟨(d.fst, w), hw⟩
  obtain ⟨n, hn⟩ := (sameCycle_inv.2 (R.sameCycle_rot d y rfl)).exists_nat_pow_eq
  refine ⟨n % minimalPeriod ⇑(R.rot⁻¹) d, Nat.mod_lt _ (R.minimalPeriod_rot_inv_pos d), ?_⟩
  have hmod : (R.rot⁻¹ ^ (n % minimalPeriod ⇑(R.rot⁻¹) d)) d = (R.rot⁻¹ ^ n) d := by
    rw [coe_pow, coe_pow]
    exact iterate_mod_minimalPeriod_eq
  rw [hmod, hn]

/-- The inverse-rotation period of `d` is `|N(d.fst)|`. -/
theorem minimalPeriod_rot_inv (d : G.Dart) :
    minimalPeriod ⇑(R.rot⁻¹) d = (G.neighborSet d.fst).ncard := by
  let g : Fin (minimalPeriod ⇑(R.rot⁻¹) d) → G.neighborSet d.fst := fun i ↦
    ⟨((R.rot⁻¹ ^ (i : ℕ)) d).snd, by
      have h := ((R.rot⁻¹ ^ (i : ℕ)) d).adj
      rw [R.fst_rot_inv_pow] at h
      exact h⟩
  have hinj : Injective g := fun i j hij ↦
    Fin.ext (R.eq_of_rot_inv_pow_snd_eq d i.isLt j.isLt (congrArg Subtype.val hij))
  have hsurj : Surjective g := by
    rintro ⟨w, hw⟩
    obtain ⟨j, hj, hjw⟩ := R.exists_rot_inv_pow_snd d hw
    exact ⟨⟨j, hj⟩, Subtype.ext hjw⟩
  have hc := Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_coe_set_eq] at hc

/-- Inverse rotation returns to `d` after `|N(d.fst)|` steps. -/
theorem rot_inv_pow_ncard (d : G.Dart) : (R.rot⁻¹ ^ (G.neighborSet d.fst).ncard) d = d := by
  rw [← R.minimalPeriod_rot_inv d, coe_pow]
  exact iterate_minimalPeriod

end RotationSystem

namespace RotationSystem

variable [Finite V] {H : SimpleGraph V} (R : RotationSystem H)

/-- The endpoints indexed by `ZMod |N(v)|` cover all neighbors of `v`. -/
theorem exists_zmod_rot_inv_pow_snd (d₀ : H.Dart) {v : V} (hd₀ : d₀.fst = v)
    [NeZero (H.neighborSet v).ncard] {z : V} (hz : H.Adj v z) :
    ∃ i : ZMod (H.neighborSet v).ncard, ((R.rot⁻¹ ^ i.val) d₀).snd = z := by
  subst hd₀
  obtain ⟨j, hj, hjz⟩ := R.exists_rot_inv_pow_snd d₀ hz
  rw [R.minimalPeriod_rot_inv] at hj
  refine ⟨(j : ZMod _), ?_⟩
  rw [ZMod.val_natCast_of_lt hj]
  exact hjz

/-- The endpoint map `i ↦ (ρ⁻¹^i.val d₀).snd` is injective on `ZMod |N(v)|`. -/
theorem eq_of_zmod_rot_inv_pow_snd_eq (d₀ : H.Dart) {v : V} (hd₀ : d₀.fst = v)
    [NeZero (H.neighborSet v).ncard] {i j : ZMod (H.neighborSet v).ncard}
    (h : ((R.rot⁻¹ ^ i.val) d₀).snd = ((R.rot⁻¹ ^ j.val) d₀).snd) : i = j := by
  subst hd₀
  have hN := R.minimalPeriod_rot_inv d₀
  have hi : i.val < minimalPeriod ⇑(R.rot⁻¹) d₀ := by
    rw [hN]
    exact ZMod.val_lt i
  have hj : j.val < minimalPeriod ⇑(R.rot⁻¹) d₀ := by
    rw [hN]
    exact ZMod.val_lt j
  exact ZMod.val_injective _ (R.eq_of_rot_inv_pow_snd_eq d₀ hi hj h)

/-- Two distinct neighbors satisfying `P` give at least two positions in `S`. -/
theorem two_le_card_of_two_adj (d₀ : H.Dart) {v : V} (hd₀ : d₀.fst = v)
    [NeZero (H.neighborSet v).ncard] (S : Finset (ZMod (H.neighborSet v).ncard))
    (P : V → Prop) (hS : ∀ i, i ∈ S ↔ P ((R.rot⁻¹ ^ i.val) d₀).snd) {a b : V} (hab : a ≠ b)
    (ha : H.Adj v a) (hb : H.Adj v b) (hPa : P a) (hPb : P b) : 2 ≤ S.card := by
  obtain ⟨i, hi⟩ := R.exists_zmod_rot_inv_pow_snd d₀ hd₀ ha
  obtain ⟨j, hj⟩ := R.exists_zmod_rot_inv_pow_snd d₀ hd₀ hb
  have hij : i ≠ j := by
    rintro rfl
    exact hab (hi.symm.trans hj)
  have hiS : i ∈ S := (hS i).2 (by rw [hi]; exact hPa)
  have hjS : j ∈ S := (hS j).2 (by rw [hj]; exact hPb)
  exact Finset.one_lt_card.2 ⟨i, hiS, j, hjS, hij⟩

end RotationSystem

end Kuratowski
