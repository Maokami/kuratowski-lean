import Kuratowski.CyclicWalk
import Mathlib.Order.Circular.ZMod
import Mathlib.Data.Finset.Max
import Mathlib.Data.ZMod.Basic

/-!
# Interval classification of cyclic words

The `X/B` positions and the `Y/B` positions are represented by two finite sets; their intersection
is the set of `B` positions.
-/

namespace Kuratowski.CyclicWord

variable {m : ℕ}

/-- Two consecutive `X` positions in the cyclic order: the endpoints are distinct and the open
arc between them contains no `X` position. -/
def Consecutive {α : Type*} [CircularOrder α] (X : Finset α) (a b : α) : Prop :=
  a ∈ X ∧ b ∈ X ∧ a ≠ b ∧ ∀ t ∈ X, ¬ sbtw a t b

private theorem gap_extremes {X : Finset (Fin m)} (hX : 2 ≤ X.card) :
    ∃ a b : Fin m, Consecutive X a b ∧
      ∀ u, (∀ x ∈ X, u < x) ∨ (∀ x ∈ X, x < u) → sbtw a u b := by
  have hne : X.Nonempty := Finset.card_pos.mp (by omega)
  let a := X.max' hne
  let b := X.min' hne
  have hba : b < a := X.min'_lt_max'_of_card (by omega)
  refine ⟨a, b, ⟨X.max'_mem hne, X.min'_mem hne, by omega, ?_⟩, ?_⟩
  · intro t ht hs
    have hlo := X.min'_le t ht
    have hhi := X.le_max' t ht
    simp only [Fin.sbtw_iff] at hs
    change b ≤ t at hlo
    change t ≤ a at hhi
    omega
  · intro u hu
    simp only [Fin.sbtw_iff]
    rcases hu with hu | hu
    · have hb := hu b (X.min'_mem hne)
      exact Or.inr (Or.inl ⟨hb, hba⟩)
    · have ha := hu a (X.max'_mem hne)
      exact Or.inr (Or.inr ⟨hba, ha⟩)

/-- A position outside `X` lies in the open arc between two consecutive `X` positions. -/
theorem exists_consecutive_gap (X : Finset (Fin m)) (hX : 2 ≤ X.card) (u : Fin m)
    (hu : u ∉ X) : ∃ a b, Consecutive X a b ∧ sbtw a u b := by
  classical
  let L := X.filter (· < u)
  let R := X.filter (u < ·)
  by_cases hL : L.Nonempty
  · by_cases hR : R.Nonempty
    · let a := L.max' hL
      let b := R.min' hR
      have ha : a ∈ X ∧ a < u := Finset.mem_filter.mp (L.max'_mem hL)
      have hb : b ∈ X ∧ u < b := Finset.mem_filter.mp (R.min'_mem hR)
      refine ⟨a, b, ⟨ha.1, hb.1, by omega, ?_⟩, Or.inl ⟨ha.2, hb.2⟩⟩
      intro t ht hs
      simp only [Fin.sbtw_iff] at hs
      have hat : a < t := by omega
      have htb : t < b := by omega
      by_cases htu : t < u
      · have htm : t ∈ L := Finset.mem_filter.mpr ⟨ht, htu⟩
        have := L.le_max' t htm
        change t ≤ a at this
        omega
      · have hne : t ≠ u := fun he ↦ hu (he ▸ ht)
        have htm : t ∈ R := Finset.mem_filter.mpr ⟨ht, by omega⟩
        have := R.min'_le t htm
        change b ≤ t at this
        omega
    · obtain ⟨a, b, hab, hext⟩ := gap_extremes hX
      refine ⟨a, b, hab, hext u (Or.inr ?_)⟩
      intro x hx
      have hne : x ≠ u := fun he ↦ hu (he ▸ hx)
      have hnot : ¬ u < x := by
        intro hux
        exact hR ⟨x, Finset.mem_filter.mpr ⟨hx, hux⟩⟩
      omega
  · obtain ⟨a, b, hab, hext⟩ := gap_extremes hX
    refine ⟨a, b, hab, hext u (Or.inl ?_)⟩
    intro x hx
    have hne : x ≠ u := fun he ↦ hu (he ▸ hx)
    have hnot : ¬ x < u := by
      intro hxu
      exact hL ⟨x, Finset.mem_filter.mpr ⟨hx, hxu⟩⟩
    omega

/-- Every `Y` position lies in the closed arc between two consecutive `X` positions. -/
def Clustered {α : Type*} [CircularOrder α] (X Y : Finset α) : Prop :=
  ∃ a b, Consecutive X a b ∧ ∀ t ∈ Y, btw a t b

/-- Each of the two open arcs between two `Y` positions contains an `X` position. -/
def Alternating {α : Type*} [CircularOrder α] (X Y : Finset α) : Prop :=
  ∃ u ∈ Y, ∃ w ∈ Y, (∃ a ∈ X, sbtw u a w) ∧ ∃ b ∈ X, sbtw w b u

private theorem gap_separates (a u b w : Fin m) (hu : sbtw a u b) (hw : ¬ btw a w b) :
    sbtw u b w ∧ sbtw w a u := by
  simp only [Fin.sbtw_iff, Fin.btw_iff] at *
  constructor <;> omega

private theorem clustered_or_alternating_of_noncommon (X Y : Finset (Fin m))
    (hX : 2 ≤ X.card) (u : Fin m) (huY : u ∈ Y) (huX : u ∉ X) :
    Clustered X Y ∨ Alternating X Y := by
  classical
  obtain ⟨a, b, hab, hu⟩ := exists_consecutive_gap X hX u huX
  by_cases hall : ∀ w ∈ Y, btw a w b
  · exact Or.inl ⟨a, b, hab, hall⟩
  · obtain ⟨w, hw⟩ := not_forall.mp hall
    obtain ⟨hwY, hwout⟩ := not_imp.mp hw
    have hsep := gap_separates a u b w hu hwout
    exact Or.inr ⟨u, huY, w, hwY, ⟨b, hab.2.1, hsep.1⟩, a, hab.1, hsep.2⟩

/-- The three cases for a cyclic word. `X ∩ Y` is the set of `B` positions. -/
theorem trichotomy_fin (X Y : Finset (Fin m)) (hX : 2 ≤ X.card) (hY : 2 ≤ Y.card) :
    Clustered X Y ∨ 3 ≤ (X ∩ Y).card ∨ Alternating X Y := by
  classical
  by_cases hex : ∃ u ∈ Y, u ∉ X
  · obtain ⟨u, huY, huX⟩ := hex
    exact (clustered_or_alternating_of_noncommon X Y hX u huY huX).elim
      Or.inl (Or.inr ∘ Or.inr)
  have hYX : Y ⊆ X := by
    intro u hu
    by_contra hn
    exact hex ⟨u, hu, hn⟩
  by_cases hthree : 3 ≤ (X ∩ Y).card
  · exact Or.inr (Or.inl hthree)
  have hinter : X ∩ Y = Y := Finset.inter_eq_right.mpr hYX
  have hcard : Y.card = 2 := by rw [hinter] at hthree; omega
  obtain ⟨u, w, huw, hYeq⟩ := Finset.card_eq_two.mp hcard
  have hu : u ∈ Y := by rw [hYeq]; simp
  have hw : w ∈ Y := by rw [hYeq]; simp
  by_cases hleft : ∃ a ∈ X, sbtw u a w
  · by_cases hright : ∃ b ∈ X, sbtw w b u
    · exact Or.inr (Or.inr ⟨u, hu, w, hw, hleft, hright⟩)
    · apply Or.inl
      refine ⟨w, u, ⟨hYX hw, hYX hu, huw.symm, ?_⟩, ?_⟩
      · intro t ht hs
        exact hright ⟨t, ht, hs⟩
      · intro t ht
        rw [hYeq, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl <;> simp only [Fin.btw_iff] <;> omega
  · apply Or.inl
    refine ⟨u, w, ⟨hYX hu, hYX hw, huw, ?_⟩, ?_⟩
    · intro t ht hs
      exact hleft ⟨t, ht, hs⟩
    · intro t ht
      rw [hYeq, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> simp only [Fin.btw_iff] <;> omega

/-- Classification of cyclic words on `ZMod m`. Words of length 2 are allowed. -/
theorem trichotomy {m : ℕ} [NeZero m] (X Y : Finset (ZMod m))
    (hX : 2 ≤ X.card) (hY : 2 ≤ Y.card) :
    Clustered X Y ∨ 3 ≤ (X ∩ Y).card ∨ Alternating X Y := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact trichotomy_fin X Y hX hY

/-- The open cyclic order on `ZMod` is strict inequality of forward modular distances. -/
theorem sbtw_iff_val {m : ℕ} [NeZero m] (a t b : ZMod m) :
    sbtw a t b ↔ 0 < (t - a).val ∧ (t - a).val < (b - a).val := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    change ((a : Fin (n + 1)).val < (t : Fin (n + 1)).val ∧
      (t : Fin (n + 1)).val < (b : Fin (n + 1)).val ∨
      (t : Fin (n + 1)).val < (b : Fin (n + 1)).val ∧
      (b : Fin (n + 1)).val < (a : Fin (n + 1)).val ∨
      (b : Fin (n + 1)).val < (a : Fin (n + 1)).val ∧
      (a : Fin (n + 1)).val < (t : Fin (n + 1)).val) ↔
      0 < (t - a : Fin (n + 1)).val ∧
        (t - a : Fin (n + 1)).val < (b - a : Fin (n + 1)).val
    have hta := Fin.intCast_val_sub_eq_sub_add_ite (t : Fin (n + 1)) a
    have hba := Fin.intCast_val_sub_eq_sub_add_ite (b : Fin (n + 1)) a
    simp only [ZMod.val] at *
    split_ifs at hta hba <;> omega

/-- An open arc of a cyclic word and the interior of the corresponding cycle path refer to the
same positions. -/
theorem mem_walkInterior_arc_iff {V : Type*} {G : SimpleGraph V} {m : ℕ}
    (C : CyclicSequence G m) (a t b : ZMod m) :
    C t ∈ walkInterior (C.arc a b) ↔ sbtw a t b := by
  have : NeZero m := C.neZero
  rw [C.mem_walkInterior_arc, sbtw_iff_val]

/-- Letters of a cyclic word. `both` is `B` and `blank` is `-`. -/
inductive Letter
  | x | y | both | blank
  deriving DecidableEq

/-- The `X/B` positions. -/
def xPositions {m : ℕ} [NeZero m] (w : ZMod m → Letter) : Finset (ZMod m) :=
  Finset.univ.filter fun i ↦ w i = .x ∨ w i = .both

/-- The `Y/B` positions. -/
def yPositions {m : ℕ} [NeZero m] (w : ZMod m → Letter) : Finset (ZMod m) :=
  Finset.univ.filter fun i ↦ w i = .y ∨ w i = .both

/-- The `B` positions. -/
def bothPositions {m : ℕ} [NeZero m] (w : ZMod m → Letter) : Finset (ZMod m) :=
  Finset.univ.filter fun i ↦ w i = .both

@[simp] theorem inter_positions {m : ℕ} [NeZero m] (w : ZMod m → Letter) :
    xPositions w ∩ yPositions w = bothPositions w := by
  ext i
  cases hw : w i <;> simp [xPositions, yPositions, bothPositions, hw]

/-- Blueprint `lem:cyclic`: the positions are clustered in an interval, there are at least three
`B` positions, or `X/B` positions alternate with `Y/B` positions across two open arcs. -/
theorem classify {m : ℕ} [NeZero m] (w : ZMod m → Letter)
    (hX : 2 ≤ (xPositions w).card) (hY : 2 ≤ (yPositions w).card) :
    Clustered (xPositions w) (yPositions w) ∨ 3 ≤ (bothPositions w).card ∨
      Alternating (xPositions w) (yPositions w) := by
  simpa only [inter_positions] using trichotomy (xPositions w) (yPositions w) hX hY

end Kuratowski.CyclicWord
