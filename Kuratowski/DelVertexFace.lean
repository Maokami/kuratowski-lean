import Kuratowski.RotationOrder
import Kuratowski.FaceCycle
import Kuratowski.VertexDeletion

/-!
# The face around a deleted vertex (blueprint `lem:J2`)

Let `R` be a genus-0 rotation system of `H`, let `v` have `N ≥ 2` neighbors, and assume
`ConnectedOn (H - v) 2 (S_H \ {v})`. Then one face of `R.delVertex v`, the rotation system with
`v` deleted, passes through the neighbors of `v` in the reverse order of the rotation around `v`
(`RotationSystem.exists_cyclicSequence_delVertex_neighbors`). The face is fixed as that of the dart
`e` with the same endpoints as `φ(d₀)`.

* The darts leaving `v` form one cycle of the rotation, so `d_j = ρ⁻¹^j d₀` has minimal period
  `N`, the number of neighbors of `v`, and the end vertices `u_j` (`j < N`) of `d_j` enumerate the
  neighbors once each (`minimalPeriod_rot_inv`, in `RotationOrder`).
* From the hypothesis `ConnectedOn (H - v) 2 (S_H \ {v})` and `N ≥ 2`, both `H - v` and `H` are
  2-connected.
* Let `L_j` be the face length of `d_j`. Then `φ^{L_j - 1} d_j` is the reverse of `d_{j+1}`, and by
  J1 the segment `P_j = (φ¹ d_j, …, φ^{L_j - 2} d_j)` does not meet `v`. Inside `P_j` the face
  permutation after deletion agrees with the original one, and from the end of `P_j` it moves to
  the first dart `φ(d_{j+1})` of `P_{j+1}` (`sector_iterate`, `sector_iterate_next`).
* By J1, the darts `d_j` for distinct `j` lie on distinct faces, so the segments share no dart.
  Hence the face of `e` has length `M = Σ_{j<N} (L_j - 2)` (`faceLength_delVertex_eq_sectorStart`),
  and `u_j` occurs at position `p_j = Σ_{t<j} (L_t - 2)`.
* `exists_cyclicSequence_face` hides the length in an existential, so we show again that the length
  of the sequence equals the face length (`eq_faceLength_of_cyclicSequence`).
-/

namespace Kuratowski

open SimpleGraph Equiv Equiv.Perm Function

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

variable (R : RotationSystem G)

variable [Finite V]

/-! ### 2-connectivity -/

variable {H : SimpleGraph V} {v : V}

/-- Under the hypothesis, the support of `H - v` is `S_H \ {v}`. -/
theorem support_deleteVertices_of_connectedOn
    (hconn : ConnectedOn (deleteVertices H {v}) 2 (H.support \ {v})) :
    (deleteVertices H {v}).support = H.support \ {v} := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hab⟩ := (mem_support _).1 ha
    exact ⟨(mem_support _).2 ⟨b, hab.1⟩, hab.2.1⟩
  · intro ha
    have h3 := hconn.1
    have hlt : ({a} : Set V).ncard < (H.support \ {v}).ncard := by
      rw [Set.ncard_singleton]
      omega
    obtain ⟨b, hb, hba⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
    have hr := hconn.2 ∅ (by simp) a ⟨ha, by simp⟩ b ⟨hb, by simp⟩
    rw [deleteVertices_empty] at hr
    obtain ⟨p⟩ := hr
    cases p with
    | nil => exact absurd rfl hba
    | cons h _ => exact (mem_support _).2 ⟨_, h⟩

/-- Under the hypothesis, `H - v` is 2-connected. -/
theorem twoConnected_deleteVertices_of_connectedOn
    (hconn : ConnectedOn (deleteVertices H {v}) 2 (H.support \ {v})) :
    TwoConnected (deleteVertices H {v}) := by
  unfold TwoConnected
  rw [support_deleteVertices_of_connectedOn hconn]
  exact hconn

/-- Under the hypothesis, and if `v` has at least two neighbors, `H` is 2-connected. -/
theorem twoConnected_of_connectedOn_deleteVertices (hdeg : 2 ≤ (H.neighborSet v).ncard)
    (hconn : ConnectedOn (deleteVertices H {v}) 2 (H.support \ {v})) : TwoConnected H := by
  refine ⟨?_, ?_⟩
  · have h3 := hconn.1
    have hsub : (H.support \ {v}).ncard ≤ H.support.ncard := Set.ncard_le_ncard Set.sdiff_subset
    omega
  · intro S hS
    -- each vertex of `S_H \ S` is connected in `H - S` to a vertex of `(S_H \ {v}) \ S`
    have hreach : ∀ u ∈ H.support \ S,
        ∃ u' ∈ (H.support \ {v}) \ S, (deleteVertices H S).Reachable u u' := by
      intro u hu
      by_cases huv : u = v
      · obtain ⟨w, hw, hwS⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (lt_of_lt_of_le hS hdeg)
        have hvS : v ∉ S := huv ▸ hu.2
        refine ⟨w, ⟨⟨(mem_support _).2 ⟨v, hw.symm⟩, fun h ↦ hw.ne.symm h⟩, hwS⟩, ?_⟩
        rw [huv]
        exact Adj.reachable ⟨hw, hvS, hwS⟩
      · exact ⟨u, ⟨⟨hu.1, huv⟩, hu.2⟩, Reachable.refl _⟩
    have hle : deleteVertices (deleteVertices H {v}) S ≤ deleteVertices H S :=
      fun x y hxy ↦ ⟨hxy.1.1, hxy.2⟩
    intro u hu w hw
    obtain ⟨u', hu', hu'r⟩ := hreach u hu
    obtain ⟨w', hw', hw'r⟩ := hreach w hw
    exact hu'r.trans (((hconn.2 S hS u' hu' w' hw').mono hle).trans hw'r.symm)

/-! ### Start vertices on a face and the good dart `e` -/

variable [DecidableEq V]

/-- For a 2-connected graph and genus 0, if `0 < i < L`, then the start vertex of `φ^i d` differs
from the start vertex of `d` (J1). -/
theorem fst_facePerm_pow_ne (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d : G.Dart) {i : ℕ} (hi : 0 < i)
    (hiL : i < R.faceLength d) : ((R.facePerm ^ i) d).fst ≠ d.fst := by
  intro h
  have hd := R.eq_of_sameCycle_facePerm_of_fst_eq hG hR
    (sameCycle_pow_left.2 (SameCycle.refl _ d)) h
  have := R.eq_of_facePerm_pow_eq hiL (R.faceLength_pos d) (by simpa using hd)
  omega

/-- If `i + 2 ≤ L`, the end vertex of `φ^i d` differs from the start vertex of `d`. -/
theorem snd_facePerm_pow_ne (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d : G.Dart) {i : ℕ}
    (hi : i + 2 ≤ R.faceLength d) : ((R.facePerm ^ i) d).snd ≠ d.fst := by
  rw [← R.facePerm_fst, ← Perm.mul_apply, ← pow_succ']
  exact R.fst_facePerm_pow_ne hG hR d (Nat.succ_pos i) (by omega)

/-- `φ(d₀)` does not meet the start vertex of `d₀`, so it transports to a dart of the graph with
that vertex deleted. -/
theorem exists_delVertex_dart_facePerm (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d₀ : G.Dart) :
    ∃ e : (deleteVertices G {d₀.fst}).Dart, e.toProd = (R.facePerm d₀).toProd := by
  have h3 := R.three_le_faceLength hG d₀
  have h2 := R.snd_facePerm_pow_ne hG hR d₀ (i := 1) (by omega)
  rw [pow_one] at h2
  refine ⟨⟨(R.facePerm d₀).toProd, (R.facePerm d₀).adj, fun h ↦ ?_, fun h ↦ h2 h⟩, rfl⟩
  exact d₀.adj.ne ((Set.mem_singleton_iff.1 h).symm.trans (R.facePerm_fst d₀))

/-! ### One step of the face permutation after deletion -/

theorem delVertex_facePerm_toProd_of_snd_ne {v : V} (x : (deleteVertices G {v}).Dart)
    (y : G.Dart) (hxy : x.toProd = y.toProd) (h : (R.facePerm y).snd ≠ v) :
    ((R.delVertex v).facePerm x).toProd = (R.facePerm y).toProd := by
  rw [R.delVertex_facePerm_toProd v x y hxy]
  have h' : ¬ (R.rot y.symm).snd = v := h
  simp [h']

theorem delVertex_facePerm_toProd_of_snd_eq {v : V} (x : (deleteVertices G {v}).Dart)
    (y : G.Dart) (hxy : x.toProd = y.toProd) (h : (R.facePerm y).snd = v) :
    ((R.delVertex v).facePerm x).toProd = (R.rot (R.facePerm y)).toProd := by
  rw [R.delVertex_facePerm_toProd v x y hxy]
  have h' : (R.rot y.symm).snd = v := h
  simp [h']

/-! ### The face segments `P_j` -/

omit [DecidableEq V] in
/-- On a face, the dart just before `d` is the reverse of `ρ⁻¹ d`. -/
theorem facePerm_pow_faceLength_sub_one (d : G.Dart) :
    (R.facePerm ^ (R.faceLength d - 1)) d = (R.rot⁻¹ d).symm := by
  apply R.facePerm.injective
  rw [← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel (R.faceLength_pos d),
    R.facePerm_pow_faceLength, facePerm_apply, Dart.symm_symm]
  simp

/-- The length `ℓ_j = L_j - 2` of the face segment `P_j` (`d_j = ρ⁻¹^j d₀`, and `L_j` is the
face length of `d_j`). -/
noncomputable def sectorLen (d₀ : G.Dart) (j : ℕ) : ℕ := R.faceLength ((R.rot⁻¹ ^ j) d₀) - 2

/-- The position `s_j = ℓ_0 + ⋯ + ℓ_{j-1}` where the segment `P_j` starts. -/
noncomputable def sectorStart (d₀ : G.Dart) (j : ℕ) : ℕ :=
  ∑ t ∈ Finset.range j, R.sectorLen d₀ t

omit [DecidableEq V] in
theorem sectorLen_pos (hG : TwoConnected G) (d₀ : G.Dart) (j : ℕ) : 0 < R.sectorLen d₀ j := by
  have := R.three_le_faceLength hG ((R.rot⁻¹ ^ j) d₀)
  unfold sectorLen
  omega

omit [Finite V] [DecidableEq V] in
theorem sectorStart_zero (d₀ : G.Dart) : R.sectorStart d₀ 0 = 0 := by
  simp [sectorStart]

omit [Finite V] [DecidableEq V] in
theorem sectorStart_succ (d₀ : G.Dart) (j : ℕ) :
    R.sectorStart d₀ (j + 1) = R.sectorStart d₀ j + R.sectorLen d₀ j :=
  Finset.sum_range_succ _ _

omit [DecidableEq V] in
theorem sectorStart_lt (hG : TwoConnected G) (d₀ : G.Dart) {j n : ℕ} (hjn : j < n) :
    R.sectorStart d₀ j < R.sectorStart d₀ n := by
  have h1 := R.sectorStart_succ d₀ j
  have h2 := R.sectorLen_pos hG d₀ j
  have h3 : R.sectorStart d₀ (j + 1) ≤ R.sectorStart d₀ n :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hjn)
  omega

omit [Finite V] [DecidableEq V] in
/-- A position below `s_n` is the `i`-th place of some segment `P_j` with `j < n`. -/
theorem exists_sector_of_lt (d₀ : G.Dart) :
    ∀ n k, k < R.sectorStart d₀ n →
      ∃ j < n, ∃ i < R.sectorLen d₀ j, k = R.sectorStart d₀ j + i := by
  intro n
  induction n with
  | zero => intro k hk; simp [sectorStart] at hk
  | succ n ih =>
    intro k hk
    rw [sectorStart_succ] at hk
    by_cases hkn : k < R.sectorStart d₀ n
    · obtain ⟨j, hj, i, hi, rfl⟩ := ih k hkn
      exact ⟨j, by omega, i, hi, rfl⟩
    · exact ⟨n, by omega, k - R.sectorStart d₀ n, by omega, by omega⟩

/-- Inside a segment, the face permutation after deletion agrees with the original face
permutation. -/
theorem sector_iterate (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d₀ : G.Dart)
    (e : (deleteVertices G {d₀.fst}).Dart) (j : ℕ)
    (hj : ((((R.delVertex d₀.fst).facePerm ^ R.sectorStart d₀ j) e).toProd =
      (R.facePerm ((R.rot⁻¹ ^ j) d₀)).toProd)) :
    ∀ i < R.sectorLen d₀ j, (((R.delVertex d₀.fst).facePerm ^ (R.sectorStart d₀ j + i)) e).toProd =
      ((R.facePerm ^ (i + 1)) ((R.rot⁻¹ ^ j) d₀)).toProd := by
  intro i
  induction i with
  | zero => intro _; simpa using hj
  | succ i ih =>
    intro hi
    have hdv : ((R.rot⁻¹ ^ j) d₀).fst = d₀.fst := R.fst_rot_inv_pow d₀ j
    have hL : i + 1 < R.faceLength ((R.rot⁻¹ ^ j) d₀) - 2 := hi
    rw [← add_assoc, pow_succ' (R.delVertex d₀.fst).facePerm, Perm.mul_apply,
      R.delVertex_facePerm_toProd_of_snd_ne _ _ (ih (by omega)) ?_, ← Perm.mul_apply,
      ← pow_succ']
    rw [← Perm.mul_apply, ← pow_succ', ← hdv]
    exact R.snd_facePerm_pow_ne hG hR _ (by omega)

/-- After the last dart of the segment `P_j` comes the first dart of `P_{j+1}`. -/
theorem sector_iterate_next (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d₀ : G.Dart)
    (e : (deleteVertices G {d₀.fst}).Dart) (j : ℕ)
    (hj : ((((R.delVertex d₀.fst).facePerm ^ R.sectorStart d₀ j) e).toProd =
      (R.facePerm ((R.rot⁻¹ ^ j) d₀)).toProd)) :
    (((R.delVertex d₀.fst).facePerm ^ R.sectorStart d₀ (j + 1)) e).toProd =
      (R.facePerm ((R.rot⁻¹ ^ (j + 1)) d₀)).toProd := by
  have hpos := R.sectorLen_pos hG d₀ j
  have hlast := R.sector_iterate hG hR d₀ e j hj (R.sectorLen d₀ j - 1) (by omega)
  have hs : R.sectorStart d₀ (j + 1) = R.sectorStart d₀ j + (R.sectorLen d₀ j - 1) + 1 := by
    rw [sectorStart_succ]
    omega
  have hy : R.facePerm ((R.facePerm ^ (R.sectorLen d₀ j - 1 + 1)) ((R.rot⁻¹ ^ j) d₀)) =
      ((R.rot⁻¹ ^ (j + 1)) d₀).symm := by
    have h3 := R.three_le_faceLength hG ((R.rot⁻¹ ^ j) d₀)
    rw [← Perm.mul_apply, ← pow_succ',
      show R.sectorLen d₀ j - 1 + 1 + 1 = R.faceLength ((R.rot⁻¹ ^ j) d₀) - 1 by
        unfold sectorLen; omega,
      R.facePerm_pow_faceLength_sub_one, pow_succ' R.rot⁻¹, Perm.mul_apply]
  have hv : (R.facePerm ((R.facePerm ^ (R.sectorLen d₀ j - 1 + 1)) ((R.rot⁻¹ ^ j) d₀))).snd =
      d₀.fst := by
    rw [hy]
    exact R.fst_rot_inv_pow d₀ (j + 1)
  rw [hs, pow_succ' (R.delVertex d₀.fst).facePerm, Perm.mul_apply,
    R.delVertex_facePerm_toProd_of_snd_eq _ _ hlast hv, hy, facePerm_apply]

/-- `φ'^{s_j} e` is the first dart `φ(d_j)` of the segment `P_j`. -/
theorem sector_iterate_start (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d₀ : G.Dart)
    (e : (deleteVertices G {d₀.fst}).Dart) (he : e.toProd = (R.facePerm d₀).toProd) (j : ℕ) :
    (((R.delVertex d₀.fst).facePerm ^ R.sectorStart d₀ j) e).toProd =
      (R.facePerm ((R.rot⁻¹ ^ j) d₀)).toProd := by
  induction j with
  | zero => simpa [sectorStart] using he
  | succ j ih => exact R.sector_iterate_next hG hR d₀ e j ih

/-- If `j ≠ j'` (both `< N`), then `d_j` and `d_j'` lie on different faces (J1). -/
theorem not_sameCycle_sector (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d₀ : G.Dart) {j j' : ℕ}
    (hj : j < (G.neighborSet d₀.fst).ncard) (hj' : j' < (G.neighborSet d₀.fst).ncard)
    (hne : j ≠ j') : ¬ R.facePerm.SameCycle ((R.rot⁻¹ ^ j) d₀) ((R.rot⁻¹ ^ j') d₀) := by
  intro h
  have heq := R.eq_of_sameCycle_facePerm_of_fst_eq hG hR h
    (by rw [R.fst_rot_inv_pow, R.fst_rot_inv_pow])
  rw [← R.minimalPeriod_rot_inv d₀] at hj hj'
  exact hne (iterate_injOn_Iio_minimalPeriod hj hj' (by simpa only [coe_pow] using heq))

/-- The darts `φ'^k e` are distinct for exponents below `M = s_N`. -/
theorem delVertex_facePerm_pow_inj (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d₀ : G.Dart)
    (e : (deleteVertices G {d₀.fst}).Dart) (he : e.toProd = (R.facePerm d₀).toProd)
    {k₁ k₂ : ℕ} (hk₁ : k₁ < R.sectorStart d₀ (G.neighborSet d₀.fst).ncard)
    (hk₂ : k₂ < R.sectorStart d₀ (G.neighborSet d₀.fst).ncard)
    (h : ((R.delVertex d₀.fst).facePerm ^ k₁) e = ((R.delVertex d₀.fst).facePerm ^ k₂) e) :
    k₁ = k₂ := by
  obtain ⟨j₁, hj₁, i₁, hi₁, rfl⟩ := R.exists_sector_of_lt d₀ _ _ hk₁
  obtain ⟨j₂, hj₂, i₂, hi₂, rfl⟩ := R.exists_sector_of_lt d₀ _ _ hk₂
  have h₁ := R.sector_iterate hG hR d₀ e j₁ (R.sector_iterate_start hG hR d₀ e he j₁) i₁ hi₁
  have h₂ := R.sector_iterate hG hR d₀ e j₂ (R.sector_iterate_start hG hR d₀ e he j₂) i₂ hi₂
  have hH : (R.facePerm ^ (i₁ + 1)) ((R.rot⁻¹ ^ j₁) d₀) =
      (R.facePerm ^ (i₂ + 1)) ((R.rot⁻¹ ^ j₂) d₀) :=
    Dart.ext _ _ (h₁.symm.trans ((congrArg Dart.toProd h).trans h₂))
  have hjj : j₁ = j₂ := by
    by_contra hne
    apply R.not_sameCycle_sector hG hR d₀ hj₁ hj₂ hne
    have a1 : R.facePerm.SameCycle ((R.rot⁻¹ ^ j₁) d₀)
        ((R.facePerm ^ (i₁ + 1)) ((R.rot⁻¹ ^ j₁) d₀)) :=
      (sameCycle_pow_left.2 (SameCycle.refl _ _)).symm
    have a2 : R.facePerm.SameCycle ((R.facePerm ^ (i₂ + 1)) ((R.rot⁻¹ ^ j₂) d₀))
        ((R.rot⁻¹ ^ j₂) d₀) :=
      sameCycle_pow_left.2 (SameCycle.refl _ _)
    rw [← hH] at a2
    exact a1.trans a2
  subst hjj
  unfold sectorLen at hi₁ hi₂
  have := R.eq_of_facePerm_pow_eq (by omega) (by omega) hH
  omega

/-- The fixed face has length `M = Σ_{j<N} (L_j - 2)`, the sum of the segment lengths. -/
theorem faceLength_delVertex_eq_sectorStart (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d₀ : G.Dart)
    (e : (deleteVertices G {d₀.fst}).Dart) (he : e.toProd = (R.facePerm d₀).toProd) :
    (R.delVertex d₀.fst).faceLength e = R.sectorStart d₀ (G.neighborSet d₀.fst).ncard := by
  set N := (G.neighborSet d₀.fst).ncard with hN
  have hNpos : 0 < N := (Set.ncard_pos (Set.toFinite _)).2 ⟨d₀.snd, d₀.adj⟩
  have hMpos : 0 < R.sectorStart d₀ N := by
    have := R.sectorStart_lt hG d₀ hNpos
    rwa [sectorStart_zero] at this
  have hper : ((R.delVertex d₀.fst).facePerm ^ R.sectorStart d₀ N) e = e := by
    apply Dart.ext
    rw [R.sector_iterate_start hG hR d₀ e he N, hN, R.rot_inv_pow_ncard, he]
  have hle : (R.delVertex d₀.fst).faceLength e ≤ R.sectorStart d₀ N :=
    IsPeriodicPt.minimalPeriod_le hMpos (by
      change (⇑(R.delVertex d₀.fst).facePerm)^[R.sectorStart d₀ N] e = e
      rw [← coe_pow]
      exact hper)
  have hpos := (R.delVertex d₀.fst).faceLength_pos e
  by_contra hne
  have := R.delVertex_facePerm_pow_inj hG hR d₀ e he (lt_of_le_of_ne hle hne) hMpos
    (by rw [(R.delVertex d₀.fst).facePerm_pow_faceLength, pow_zero, Perm.one_apply])
  omega

/-! ### The length of the cyclic sequence and the main theorem -/

/-- The length of a cyclic sequence following a face is the face length.
`exists_cyclicSequence_face` hides the length in an existential, so we recover it from the
sequence (by J1, `φ^m d = d`). -/
theorem eq_faceLength_of_cyclicSequence (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d : G.Dart) {m : ℕ}
    (C : CyclicSequence G m) (hC : ∀ k : ℕ, C (k : ZMod m) = ((R.facePerm ^ k) d).fst) :
    m = R.faceLength d := by
  have := C.neZero
  have h0 : C 0 = d.fst := by simpa using hC 0
  apply Nat.dvd_antisymm
  · have hL := hC (R.faceLength d)
    rw [R.facePerm_pow_faceLength, ← h0, C.apply_eq_iff] at hL
    exact (ZMod.natCast_eq_zero_iff _ _).1 hL
  · have hm := hC m
    rw [ZMod.natCast_self, h0] at hm
    have heq := R.eq_of_sameCycle_facePerm_of_fst_eq hG hR
      (sameCycle_pow_left.2 (SameCycle.refl _ d)) hm.symm
    exact IsPeriodicPt.minimalPeriod_dvd (by
      change (⇑R.facePerm)^[m] d = d
      rw [← coe_pow]
      exact heq)

/-- Blueprint `lem:J2`. Let `R` be a genus-0 rotation system. If `v` has at least two neighbors
and `S_H \ {v}` is 2-connected in `H - v`, then in the actual rotation system `R.delVertex v`,
the face of the dart `e` with the same endpoints as `φ(d₀)` is a cyclic vertex sequence `C`. It
passes through the neighbors `u_j = (ρ⁻¹^j d₀).snd` of `v`, in the reverse order of the rotation
around `v`, at positions `p_0 = 0 < p_1 < ⋯ < p_{N-1} < m`. -/
theorem exists_cyclicSequence_delVertex_neighbors {H : SimpleGraph V} (R : RotationSystem H)
    (hR : R.eulerChar = 2 * Nat.card H.ConnectedComponent) (v : V)
    (hdeg : 2 ≤ (H.neighborSet v).ncard)
    (hconn : ConnectedOn (deleteVertices H {v}) 2 (H.support \ {v}))
    (d₀ : H.Dart) (hd₀ : d₀.fst = v) :
    ∃ (e : (deleteVertices H {v}).Dart) (m : ℕ) (C : CyclicSequence (deleteVertices H {v}) m),
      e.toProd = (R.facePerm d₀).toProd ∧
      (∀ k : ℕ, C (k : ZMod m) = (((R.delVertex v).facePerm ^ k) e).fst) ∧
      ∃ p : ℕ → ℕ, p 0 = 0 ∧
        (∀ j, j + 1 < (H.neighborSet v).ncard → p j < p (j + 1)) ∧
        (∀ j, j < (H.neighborSet v).ncard → p j < m) ∧
        ∀ j, j < (H.neighborSet v).ncard → C (p j : ZMod m) = ((R.rot⁻¹ ^ j) d₀).snd := by
  have hG := twoConnected_of_connectedOn_deleteVertices hdeg hconn
  have hG' := twoConnected_deleteVertices_of_connectedOn hconn
  have hR' := R.eulerChar_delVertex v hR
  subst hd₀
  obtain ⟨e, he⟩ := R.exists_delVertex_dart_facePerm hG hR d₀
  obtain ⟨m, C, hC⟩ := (R.delVertex d₀.fst).exists_cyclicSequence_face hG' hR' e
  have hm := (R.delVertex d₀.fst).eq_faceLength_of_cyclicSequence hG' hR' e C hC
  rw [R.faceLength_delVertex_eq_sectorStart hG hR d₀ e he] at hm
  refine ⟨e, m, C, he, hC, R.sectorStart d₀, R.sectorStart_zero d₀,
    fun j _ ↦ R.sectorStart_lt hG d₀ (Nat.lt_succ_self j), fun j hj ↦ ?_, fun j _ ↦ ?_⟩
  · rw [hm]
    exact R.sectorStart_lt hG d₀ hj
  · rw [hC, ← R.facePerm_fst]
    exact congrArg Prod.fst (R.sector_iterate_start hG hR d₀ e he j)

end RotationSystem

end Kuratowski
