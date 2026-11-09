import Kuratowski.FaceCycle
import Kuratowski.VertexDeletion

/-!
# 지운 꼭짓점 둘레의 면 (블루프린트 `lem:J2`)

종수 0 회전 체계 `R`에서 꼭짓점 `v`를 지운 회전 체계 `R.delVertex v`의 면 하나가 `v`의 이웃을
`v` 둘레 회전의 역순으로 지난다 (`RotationSystem.exists_cyclicSequence_delVertex_neighbors`).
면은 `φ(d₀)`와 양 끝이 같은 다트 `e`로 고정한다.

* `v`에서 나가는 다트는 회전의 한 순환이므로 `d_j = ρ⁻¹^j d₀`의 최소 주기는 `v`의 이웃 수 `N`이고,
  `d_j`의 끝점 `u_j`(`j < N`)는 이웃을 한 번씩 열거한다 (`minimalPeriod_rot_inv`).
* 가정 `ConnectedOn (H - v) 2 (S_H \ {v})`와 `N ≥ 2`에서 `H - v`와 `H`가 모두 2-연결이다.
* `L_j`를 `d_j`의 면 길이라 하면 `φ^{L_j - 1} d_j`는 `d_{j+1}`의 역다트이고, J1에서
  `P_j = (φ¹ d_j, …, φ^{L_j - 2} d_j)`는 `v`에 닿지 않는다. 지운 회전의 면 순열은 `P_j` 안에서 원래
  면 순열과 같고, `P_j`의 끝에서 `P_{j+1}`의 첫 다트 `φ(d_{j+1})`로 넘어간다 (`sector_iterate`,
  `sector_iterate_next`).
* 서로 다른 `j`의 `d_j`는 J1에서 서로 다른 면에 있으므로 조각들은 다트를 공유하지 않는다. 따라서
  `e`의 면 길이는 `M = Σ_{j<N} (L_j - 2)`이고 (`faceLength_delVertex_eq_sectorStart`), `u_j`의 위치는
  `p_j = Σ_{t<j} (L_t - 2)`다.
* `exists_cyclicSequence_face`는 길이를 존재로 감추므로, 수열에서 길이가 면 길이와 같음을 다시
  보인다 (`eq_faceLength_of_cyclicSequence`).
-/

namespace Kuratowski

open SimpleGraph Equiv Equiv.Perm Function

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

variable (R : RotationSystem G)

/-! ### `v` 둘레의 회전: 주기와 이웃 열거 -/

/-- 회전의 역도 다트의 시작점을 보존한다. -/
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
/-- 최소 주기 아래에서 `ρ⁻¹^j d`의 끝점은 서로 다르다. -/
theorem eq_of_rot_inv_pow_snd_eq (d : G.Dart) {i j : ℕ} (hi : i < minimalPeriod ⇑(R.rot⁻¹) d)
    (hj : j < minimalPeriod ⇑(R.rot⁻¹) d) (h : ((R.rot⁻¹ ^ i) d).snd = ((R.rot⁻¹ ^ j) d).snd) :
    i = j := by
  have hd : (R.rot⁻¹ ^ i) d = (R.rot⁻¹ ^ j) d :=
    Dart.ext _ _ (Prod.ext (by rw [R.fst_rot_inv_pow, R.fst_rot_inv_pow]) h)
  exact iterate_injOn_Iio_minimalPeriod hi hj (by simpa only [coe_pow] using hd)

/-- `d`의 시작점의 이웃은 모두 최소 주기 아래의 어떤 `ρ⁻¹^j d`의 끝점이다. -/
theorem exists_rot_inv_pow_snd (d : G.Dart) {w : V} (hw : G.Adj d.fst w) :
    ∃ j < minimalPeriod ⇑(R.rot⁻¹) d, ((R.rot⁻¹ ^ j) d).snd = w := by
  let y : G.Dart := ⟨(d.fst, w), hw⟩
  obtain ⟨n, hn⟩ := (sameCycle_inv.2 (R.sameCycle_rot d y rfl)).exists_nat_pow_eq
  refine ⟨n % minimalPeriod ⇑(R.rot⁻¹) d, Nat.mod_lt _ (R.minimalPeriod_rot_inv_pos d), ?_⟩
  have hmod : (R.rot⁻¹ ^ (n % minimalPeriod ⇑(R.rot⁻¹) d)) d = (R.rot⁻¹ ^ n) d := by
    rw [coe_pow, coe_pow]
    exact iterate_mod_minimalPeriod_eq
  rw [hmod, hn]

/-- 회전의 역에서 `d`의 최소 주기는 `d`의 시작점의 이웃 수다. -/
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

/-- 시작점의 이웃 수만큼 회전의 역을 돌리면 제자리다. -/
theorem rot_inv_pow_ncard (d : G.Dart) : (R.rot⁻¹ ^ (G.neighborSet d.fst).ncard) d = d := by
  rw [← R.minimalPeriod_rot_inv d, coe_pow]
  exact iterate_minimalPeriod

/-! ### 2-연결성 -/

variable {H : SimpleGraph V} {v : V}

/-- 가정에서 `H - v`의 지지 집합은 `S_H \ {v}`다. -/
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

/-- 가정에서 `H - v`는 2-연결이다. -/
theorem twoConnected_deleteVertices_of_connectedOn
    (hconn : ConnectedOn (deleteVertices H {v}) 2 (H.support \ {v})) :
    TwoConnected (deleteVertices H {v}) := by
  unfold TwoConnected
  rw [support_deleteVertices_of_connectedOn hconn]
  exact hconn

/-- 가정과 `v`의 이웃이 둘 이상이라는 조건에서 `H`는 2-연결이다. -/
theorem twoConnected_of_connectedOn_deleteVertices (hdeg : 2 ≤ (H.neighborSet v).ncard)
    (hconn : ConnectedOn (deleteVertices H {v}) 2 (H.support \ {v})) : TwoConnected H := by
  refine ⟨?_, ?_⟩
  · have h3 := hconn.1
    have hsub : (H.support \ {v}).ncard ≤ H.support.ncard := Set.ncard_le_ncard Set.sdiff_subset
    omega
  · intro S hS
    -- `S_H \ S`의 각 점은 `H - S`에서 `(S_H \ {v}) \ S`의 점과 이어진다
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

/-! ### 면 위의 시작점과 좋은 다트 `e` -/

variable [DecidableEq V]

/-- 2-연결 종수 0에서 `0 < i < L`이면 `φ^i d`의 시작점은 `d`의 시작점과 다르다 (J1). -/
theorem fst_facePerm_pow_ne (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d : G.Dart) {i : ℕ} (hi : 0 < i)
    (hiL : i < R.faceLength d) : ((R.facePerm ^ i) d).fst ≠ d.fst := by
  intro h
  have hd := R.eq_of_sameCycle_facePerm_of_fst_eq hG hR
    (sameCycle_pow_left.2 (SameCycle.refl _ d)) h
  have := R.eq_of_facePerm_pow_eq hiL (R.faceLength_pos d) (by simpa using hd)
  omega

/-- `i + 2 ≤ L`이면 `φ^i d`의 끝점은 `d`의 시작점과 다르다. -/
theorem snd_facePerm_pow_ne (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d : G.Dart) {i : ℕ}
    (hi : i + 2 ≤ R.faceLength d) : ((R.facePerm ^ i) d).snd ≠ d.fst := by
  rw [← R.facePerm_fst, ← Perm.mul_apply, ← pow_succ']
  exact R.fst_facePerm_pow_ne hG hR d (Nat.succ_pos i) (by omega)

/-- `φ(d₀)`는 `d₀`의 시작점에 닿지 않으므로 그 점을 지운 그래프의 다트로 옮길 수 있다. -/
theorem exists_delVertex_dart_facePerm (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d₀ : G.Dart) :
    ∃ e : (deleteVertices G {d₀.fst}).Dart, e.toProd = (R.facePerm d₀).toProd := by
  have h3 := R.three_le_faceLength hG d₀
  have h2 := R.snd_facePerm_pow_ne hG hR d₀ (i := 1) (by omega)
  rw [pow_one] at h2
  refine ⟨⟨(R.facePerm d₀).toProd, (R.facePerm d₀).adj, fun h ↦ ?_, fun h ↦ h2 h⟩, rfl⟩
  exact d₀.adj.ne ((Set.mem_singleton_iff.1 h).symm.trans (R.facePerm_fst d₀))

/-! ### 지운 회전 체계의 면 순열 한 걸음 -/

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

/-! ### 면 조각 `P_j` -/

omit [DecidableEq V] in
/-- 면에서 `d` 바로 앞의 다트는 `ρ⁻¹ d`의 역다트다. -/
theorem facePerm_pow_faceLength_sub_one (d : G.Dart) :
    (R.facePerm ^ (R.faceLength d - 1)) d = (R.rot⁻¹ d).symm := by
  apply R.facePerm.injective
  rw [← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel (R.faceLength_pos d),
    R.facePerm_pow_faceLength, facePerm_apply, Dart.symm_symm]
  simp

/-- 면 조각 `P_j`의 길이 `ℓ_j = L_j - 2` (`d_j = ρ⁻¹^j d₀`, `L_j`는 `d_j`의 면 길이). -/
noncomputable def sectorLen (d₀ : G.Dart) (j : ℕ) : ℕ := R.faceLength ((R.rot⁻¹ ^ j) d₀) - 2

/-- 조각 `P_j`가 시작하는 위치 `s_j = ℓ_0 + ⋯ + ℓ_{j-1}`. -/
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
/-- `s_n`보다 작은 위치는 어떤 조각 `P_j` (`j < n`)의 `i`번째 자리다. -/
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

/-- 조각 안에서는 지운 회전의 면 순열이 원래 면 순열과 같다. -/
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

/-- 조각 `P_j`의 마지막 다트 다음은 조각 `P_{j+1}`의 첫 다트다. -/
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

/-- `φ'^{s_j} e`는 조각 `P_j`의 첫 다트 `φ(d_j)`다. -/
theorem sector_iterate_start (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d₀ : G.Dart)
    (e : (deleteVertices G {d₀.fst}).Dart) (he : e.toProd = (R.facePerm d₀).toProd) (j : ℕ) :
    (((R.delVertex d₀.fst).facePerm ^ R.sectorStart d₀ j) e).toProd =
      (R.facePerm ((R.rot⁻¹ ^ j) d₀)).toProd := by
  induction j with
  | zero => simpa [sectorStart] using he
  | succ j ih => exact R.sector_iterate_next hG hR d₀ e j ih

/-- `j ≠ j'`(`< N`)이면 `d_j`, `d_j'`은 서로 다른 면에 있다 (J1). -/
theorem not_sameCycle_sector (hG : TwoConnected G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) (d₀ : G.Dart) {j j' : ℕ}
    (hj : j < (G.neighborSet d₀.fst).ncard) (hj' : j' < (G.neighborSet d₀.fst).ncard)
    (hne : j ≠ j') : ¬ R.facePerm.SameCycle ((R.rot⁻¹ ^ j) d₀) ((R.rot⁻¹ ^ j') d₀) := by
  intro h
  have heq := R.eq_of_sameCycle_facePerm_of_fst_eq hG hR h
    (by rw [R.fst_rot_inv_pow, R.fst_rot_inv_pow])
  rw [← R.minimalPeriod_rot_inv d₀] at hj hj'
  exact hne (iterate_injOn_Iio_minimalPeriod hj hj' (by simpa only [coe_pow] using heq))

/-- `M = s_N`보다 작은 지수에서 `φ'^k e`는 서로 다르다. -/
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

/-- 고정한 면의 길이는 조각 길이의 합 `M = Σ_{j<N} (L_j - 2)`이다. -/
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

/-! ### 순환 수열의 길이와 주정리 -/

/-- 면을 따라가는 순환 수열의 길이는 그 면의 길이다. `exists_cyclicSequence_face`가 길이를
존재로 감추므로, 수열에서 길이를 되찾는다 (J1로 `φ^m d = d`). -/
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

/-- 블루프린트 `lem:J2`. `v`의 이웃이 둘 이상이고 `S_H \ {v}`가 `H - v`에서 2-연결이면, 실제 지운
회전 체계 `R.delVertex v`에서 `φ(d₀)`와 양 끝이 같은 다트 `e`의 면은 순환 꼭짓점 수열 `C`이고,
`v` 둘레 회전의 역순 이웃 `u_j = (ρ⁻¹^j d₀).snd`를 위치 `p_0 = 0 < p_1 < ⋯ < p_{N-1} < m`에서 지난다. -/
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
