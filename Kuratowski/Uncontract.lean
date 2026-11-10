import Kuratowski.ContractCounts
import Kuratowski.RotationOrder
import Kuratowski.PermutationDeletion

/-!
# Undoing the contraction of an edge without common neighbors (blueprint `lem:uncontract`)

Let `x ∼ y` in `G` with no common neighbor of `x` and `y`, and let `R'` be a rotation system of
`G/xy`. Classify the neighbors of `x` in `G/xy` by adjacency in `G`: each is adjacent in `G` to
exactly one of `x`, `y`. If, around `x`, they split into an `x`-arc of neighbors of `x` and a
`y`-arc of neighbors of `y` (vertices adjacent only to `y` in `G`), we build a rotation system of
`G` with the same number of face cycles.

* Dart bijection `uncontractDartEquiv`: replacing `y` by `x` maps the darts of `G` other than
  `(x, y)`, `(y, x)` bijectively to the darts of `G/xy` (since there is no common neighbor).
* Rotation: transport `ρ'` along the bijection, add `xy` and `yx` as fixed points, and multiply by
  three conditional transpositions.
-/

namespace Kuratowski

open SimpleGraph Equiv Equiv.Perm Function

/-! ### Conditional transpositions and cycle counts -/

section CSwap

variable {α : Type*} [DecidableEq α]

/-- The transposition if the condition holds, and the identity otherwise. -/
def cswap (c : Prop) [Decidable c] (a b : α) : Perm α := if c then swap a b else 1

theorem cswap_pos {c : Prop} [Decidable c] (h : c) (a b : α) : cswap c a b = swap a b := by
  simp [cswap, h]

theorem cswap_neg {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : cswap c a b = 1 := by
  simp [cswap, h]

theorem cswap_apply_of_ne (c : Prop) [Decidable c] {a b d : α} (ha : d ≠ a) (hb : d ≠ b) :
    cswap c a b d = d := by
  unfold cswap
  split_ifs
  · exact swap_apply_of_ne_of_ne ha hb
  · rfl

/-- Conjugating by an involution `σ` moves the two points of a conditional transposition by
`σ`. -/
theorem mul_cswap_mul_involutive (f σ : Perm α) (hσ : Involutive σ) (c : Prop) [Decidable c]
    (a b : α) : f * cswap c a b * σ = f * σ * cswap c (σ a) (σ b) := by
  unfold cswap
  split_ifs
  · ext d
    simp only [Perm.mul_apply]
    have h := hσ.injective.map_swap (σ a) (σ b) d
    rw [hσ a, hσ b] at h
    rw [h]
  · simp

variable [Finite α]

/-- Swapping a point `u` outside the 2-cycle `(p q)` with `q` merges cycles, decreasing their
number by one. -/
theorem orbitCount_mul_swap_two_cycle (f : Perm α) {p q u : α} (hpq : f p = q) (hqp : f q = p)
    (hup : u ≠ p) (huq : u ≠ q) : orbitCount (f * swap u q) + 1 = orbitCount f :=
  orbitCount_mul_swap_of_not_sameCycle fun h ↦
    PermutationDeletion.not_sameCycle_of_two_cycle f hqp hpq huq hup h.symm

/-- For distinct points `u`, `w` outside the 2-cycle `(p q)`, multiplying by `(u w)`, `(u q)`,
`(w p)` in turn decreases the number of cycles by one: split, merge, merge if `u` and `w` lie in
the same cycle, and merge, merge, split otherwise. -/
theorem orbitCount_three_swaps (f : Perm α) {p q u w : α} (hpq : f p = q) (hqp : f q = p)
    (hup : u ≠ p) (huq : u ≠ q) (hwp : w ≠ p) (hwq : w ≠ q) (huw : u ≠ w) :
    orbitCount (f * swap u w * swap u q * swap w p) + 1 = orbitCount f := by
  have hf₁p : (f * swap u w) p = q := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hup.symm hwp.symm, hpq]
  have hf₁q : (f * swap u w) q = p := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne huq.symm hwq.symm, hqp]
  have hn2 : ¬ (f * swap u w).SameCycle u q := fun h ↦
    PermutationDeletion.not_sameCycle_of_two_cycle _ hf₁q hf₁p huq hup h.symm
  by_cases hs : f.SameCycle u w
  · have h1 := orbitCount_mul_swap_of_sameCycle huw hs
    have hn1 := not_sameCycle_mul_swap_of_sameCycle huw hs
    have h2 := orbitCount_mul_swap_of_not_sameCycle hn2
    have hn3 : ¬ (f * swap u w * swap u q).SameCycle w p := by
      rw [sameCycle_iff_of_mul_swap_not hn2]
      rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · exact PermutationDeletion.not_sameCycle_of_two_cycle _ hf₁p hf₁q hwp hwq h.symm
      · exact hn1 h.symm
      · exact PermutationDeletion.not_sameCycle_of_two_cycle _ hf₁q hf₁p hwq hwp h.symm
    have h3 := orbitCount_mul_swap_of_not_sameCycle hn3
    omega
  · have h1 := orbitCount_mul_swap_of_not_sameCycle hs
    have hc : (f * swap u w).SameCycle w u := (sameCycle_mul_swap_of_not hs).symm
    have hd : (f * swap u w).SameCycle p q := ⟨1, by simpa using hf₁p⟩
    have h2 := PermutationDeletion.orbitCount_two_swaps _ hn2 hc hd hwp
    omega

end CSwap

/-! ### The dart bijection -/

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}

/-- Darts of `G` other than `(x, y)` and `(y, x)`. -/
abbrev UncontractDart (G : SimpleGraph V) (x y : V) :=
  {d : G.Dart // d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x)}

theorem contractEdge_adj_contractDart (hxy : G.Adj x y) (d : UncontractDart G x y) :
    (contractEdge G x y).Adj (contractVertex x y d.1.fst) (contractVertex x y d.1.snd) := by
  obtain ⟨⟨⟨p, q⟩, h⟩, h1, h2⟩ := d
  change (contractEdge G x y).Adj (contractVertex x y p) (contractVertex x y q)
  change G.Adj p q at h
  change (p, q) ≠ (x, y) at h1
  change (p, q) ≠ (y, x) at h2
  rw [contractEdge_adj]
  by_cases hp : p = y
  · have hq : q ≠ y := fun hq ↦ h.ne (hp.trans hq.symm)
    have hqx : q ≠ x := fun hqx ↦ h2 (by rw [hp, hqx])
    rw [hp, contractVertex_self, contractVertex_of_ne hq]
    exact ⟨fun h' ↦ hqx h'.symm, hxy.ne, hq, Or.inr (Or.inl ⟨rfl, hp ▸ h⟩)⟩
  · by_cases hq : q = y
    · have hpx : p ≠ x := fun hpx ↦ h1 (by rw [hpx, hq])
      rw [hq, contractVertex_self, contractVertex_of_ne hp]
      exact ⟨hpx, hp, hxy.ne, Or.inr (Or.inr ⟨rfl, (hq ▸ h).symm⟩)⟩
    · rw [contractVertex_of_ne hp, contractVertex_of_ne hq]
      exact ⟨h.ne, hp, hq, Or.inl h⟩

/-- The dart map: replace `y` by `x` at both ends. -/
def contractDart (hxy : G.Adj x y) (d : UncontractDart G x y) : (contractEdge G x y).Dart :=
  ⟨(contractVertex x y d.1.fst, contractVertex x y d.1.snd), contractEdge_adj_contractDart hxy d⟩

theorem contractDart_injective (hxy : G.Adj x y) (hcommon : ∀ z, ¬ (G.Adj x z ∧ G.Adj y z)) :
    Injective (contractDart hxy) := by
  rintro ⟨⟨⟨p₁, p₂⟩, hp⟩, hp₁, hp₂⟩ ⟨⟨⟨q₁, q₂⟩, hq⟩, hq₁, hq₂⟩ h
  have h₁ : contractVertex x y p₁ = contractVertex x y q₁ := congrArg (·.toProd.1) h
  have h₂ : contractVertex x y p₂ = contractVertex x y q₂ := congrArg (·.toProd.2) h
  change G.Adj p₁ p₂ at hp
  change G.Adj q₁ q₂ at hq
  change (p₁, p₂) ≠ (x, y) at hp₁
  change (p₁, p₂) ≠ (y, x) at hp₂
  apply Subtype.ext
  apply Dart.ext
  change (p₁, p₂) = (q₁, q₂)
  rcases contractVertex_eq_cases h₁ with e₁ | ⟨a₁, b₁⟩ | ⟨a₁, b₁⟩ <;>
    rcases contractVertex_eq_cases h₂ with e₂ | ⟨a₂, b₂⟩ | ⟨a₂, b₂⟩
  · rw [e₁, e₂]
  · -- `p₁ = q₁` would be a common neighbor of `x` and `y`
    refine absurd ⟨?_, ?_⟩ (hcommon p₁)
    · rw [e₁, ← b₂]; exact hq.symm
    · rw [← a₂]; exact hp.symm
  · refine absurd ⟨?_, ?_⟩ (hcommon p₁)
    · rw [← a₂]; exact hp.symm
    · rw [e₁, ← b₂]; exact hq.symm
  · refine absurd ⟨?_, ?_⟩ (hcommon p₂)
    · rw [e₂, ← b₁]; exact hq
    · rw [← a₁]; exact hp
  · exact absurd (a₁.trans a₂.symm) hp.ne
  · exact absurd (by rw [a₁, a₂]) hp₂
  · refine absurd ⟨?_, ?_⟩ (hcommon p₂)
    · rw [← a₁]; exact hp
    · rw [e₂, ← b₁]; exact hq
  · exact absurd (by rw [a₁, a₂]) hp₁
  · exact absurd (a₁.trans a₂.symm) hp.ne

theorem contractDart_surjective (hxy : G.Adj x y) : Surjective (contractDart hxy) := by
  rintro ⟨⟨a, b⟩, h⟩
  obtain ⟨hab, ha, hb, hG | ⟨hax, hG⟩ | ⟨hbx, hG⟩⟩ := (contractEdge_adj (G := G)).1 h
  · refine ⟨⟨⟨(a, b), hG⟩, fun h' ↦ hb (congrArg Prod.snd h'), fun h' ↦ ha (congrArg Prod.fst h')⟩,
      ?_⟩
    apply Dart.ext
    change (contractVertex x y a, contractVertex x y b) = (a, b)
    rw [contractVertex_of_ne ha, contractVertex_of_ne hb]
  · refine ⟨⟨⟨(y, b), hG⟩, fun h' ↦ hxy.ne (congrArg Prod.fst h').symm,
      fun h' ↦ hab (hax.trans (congrArg Prod.snd h').symm)⟩, ?_⟩
    apply Dart.ext
    change (contractVertex x y y, contractVertex x y b) = (a, b)
    rw [contractVertex_self, contractVertex_of_ne hb]
    exact Prod.ext hax.symm rfl
  · refine ⟨⟨⟨(a, y), hG.symm⟩, fun h' ↦ hab ((congrArg Prod.fst h').trans hbx.symm),
      fun h' ↦ hxy.ne (congrArg Prod.snd h').symm⟩, ?_⟩
    apply Dart.ext
    change (contractVertex x y a, contractVertex x y y) = (a, b)
    rw [contractVertex_self, contractVertex_of_ne ha]
    exact Prod.ext rfl hbx.symm

/-- Public API: without common neighbors, the darts of `G` other than `(x, y)`, `(y, x)` are in
bijection with the darts of `G/xy`. -/
noncomputable def uncontractDartEquiv (hxy : G.Adj x y) (hcommon : ∀ z, ¬ (G.Adj x z ∧ G.Adj y z)) :
    UncontractDart G x y ≃ (contractEdge G x y).Dart :=
  Equiv.ofBijective _ ⟨contractDart_injective hxy hcommon, contractDart_surjective hxy⟩

@[simp] theorem uncontractDartEquiv_toProd (hxy : G.Adj x y)
    (hcommon : ∀ z, ¬ (G.Adj x z ∧ G.Adj y z)) (d : UncontractDart G x y) :
    (uncontractDartEquiv hxy hcommon d).toProd =
      (contractVertex x y d.1.fst, contractVertex x y d.1.snd) := rfl

theorem uncontractDartEquiv_symm (hxy : G.Adj x y) (hcommon : ∀ z, ¬ (G.Adj x z ∧ G.Adj y z))
    (d : UncontractDart G x y) :
    uncontractDartEquiv hxy hcommon ⟨d.1.symm, fun h ↦ d.2.2 (by
      simpa using congrArg Prod.swap h), fun h ↦ d.2.1 (by simpa using congrArg Prod.swap h)⟩ =
      (uncontractDartEquiv hxy hcommon d).symm := rfl


/-! ### The uncontracted rotation -/

/-- Data for undoing a contraction: a rotation `R'` of `G/xy`, a dart `d₀` leaving `x`, and an
arc length `k`, such that `u_j = (ρ'⁻¹^j d₀).snd` is a neighbor of `x` in `G` for `j < k` and a
neighbor of `y` for `k ≤ j < N`. -/
structure UncontractData (G : SimpleGraph V) (x y : V) where
  hxy : G.Adj x y
  hcommon : ∀ z, ¬ (G.Adj x z ∧ G.Adj y z)
  R' : RotationSystem (contractEdge G x y)
  d₀ : (contractEdge G x y).Dart
  hd₀ : d₀.fst = x
  k : ℕ
  hk : k ≤ ((contractEdge G x y).neighborSet x).ncard
  hA : ∀ j < k, G.Adj x ((R'.rot⁻¹ ^ j) d₀).snd
  hY : ∀ j, k ≤ j → j < ((contractEdge G x y).neighborSet x).ncard →
    G.Adj y ((R'.rot⁻¹ ^ j) d₀).snd

namespace UncontractData

variable (D : UncontractData G x y)

/-- The number of neighbors of `x` in `G/xy`. -/
noncomputable abbrev N (_ : UncontractData G x y) : ℕ := ((contractEdge G x y).neighborSet x).ncard

/-- The dart `(x, y)`. -/
def xyDart : G.Dart := ⟨(x, y), D.hxy⟩

/-- The dart `(y, x)`. -/
def yxDart : G.Dart := ⟨(y, x), D.hxy.symm⟩

/-- The dart bijection. -/
noncomputable def equiv : UncontractDart G x y ≃ (contractEdge G x y).Dart :=
  uncontractDartEquiv D.hxy D.hcommon

/-- The `j`-th dart `ρ'⁻¹^j d₀` around `x`. -/
def kd (j : ℕ) : (contractEdge G x y).Dart := (D.R'.rot⁻¹ ^ j) D.d₀

/-- The dart of `G` corresponding to `kd j`. -/
noncomputable def lift (j : ℕ) : G.Dart := (D.equiv.symm (D.kd j)).1

theorem lift_mem (j : ℕ) : (D.lift j).toProd ≠ (x, y) ∧ (D.lift j).toProd ≠ (y, x) :=
  (D.equiv.symm (D.kd j)).2

/-- `ρ'` transported along the bijection; `xy` and `yx` are fixed points. -/
noncomputable def τ : Perm G.Dart := Perm.ofSubtype (D.equiv.symm.permCongr D.R'.rot)

omit [DecidableEq V] in
theorem k_le_N : D.k ≤ D.N := D.hk

omit [DecidableEq V] in
theorem kd_fst (j : ℕ) : (D.kd j).fst = x := by
  rw [kd, RotationSystem.fst_rot_inv_pow, D.hd₀]

omit [DecidableEq V] in
theorem kd_snd_ne_y (j : ℕ) : (D.kd j).snd ≠ y := (D.kd j).adj.2.2.1

omit [DecidableEq V] in
theorem kd_snd_ne_x (j : ℕ) : (D.kd j).snd ≠ x := fun h ↦
  (D.kd j).adj.1 ((D.kd_fst j).trans h.symm)

omit [DecidableEq V] in
theorem kd_succ (j : ℕ) : D.kd (j + 1) = D.R'.rot⁻¹ (D.kd j) := by
  rw [kd, kd, pow_succ', Perm.mul_apply]

omit [DecidableEq V] in
theorem rot_kd_succ (j : ℕ) : D.R'.rot (D.kd (j + 1)) = D.kd j := by
  rw [kd_succ]
  simp

omit [DecidableEq V] in
theorem xyDart_ne_yxDart : D.xyDart ≠ D.yxDart := fun h ↦ D.hxy.ne (congrArg (·.fst) h)

theorem lift_ne_xy (j : ℕ) : D.lift j ≠ D.xyDart := fun h ↦ (D.lift_mem j).1 (by rw [h]; rfl)

theorem lift_ne_yx (j : ℕ) : D.lift j ≠ D.yxDart := fun h ↦ (D.lift_mem j).2 (by rw [h]; rfl)

theorem lift_fst_mem (j : ℕ) : (D.lift j).fst = x ∨ (D.lift j).fst = y := by
  apply contractVertex_eq_x
  have h : D.equiv (D.equiv.symm (D.kd j)) = D.kd j := D.equiv.apply_symm_apply _
  have h' := congrArg (·.toProd.1) h
  exact h'.trans (D.kd_fst j)

/-- If `j < k`, the dart corresponding to `kd j` is `(x, u_j)`. -/
theorem lift_toProd_of_lt {j : ℕ} (hj : j < D.k) : (D.lift j).toProd = (x, (D.kd j).snd) := by
  have h : D.equiv ⟨⟨(x, (D.kd j).snd), D.hA j hj⟩, fun h ↦ D.kd_snd_ne_y j (congrArg Prod.snd h),
      fun h ↦ D.hxy.ne (congrArg Prod.fst h)⟩ = D.kd j := by
    apply Dart.ext
    change (contractVertex x y x, contractVertex x y (D.kd j).snd) = (D.kd j).toProd
    rw [contractVertex_of_ne D.hxy.ne, contractVertex_of_ne (D.kd_snd_ne_y j)]
    exact Prod.ext (D.kd_fst j).symm rfl
  have h' := (Equiv.symm_apply_eq D.equiv).2 h.symm
  unfold lift
  rw [h']

/-- If `k ≤ j < N`, the dart corresponding to `kd j` is `(y, u_j)`. -/
theorem lift_toProd_of_ge {j : ℕ} (hkj : D.k ≤ j) (hj : j < D.N) :
    (D.lift j).toProd = (y, (D.kd j).snd) := by
  have h : D.equiv ⟨⟨(y, (D.kd j).snd), D.hY j hkj hj⟩,
      fun h ↦ D.hxy.ne (congrArg Prod.fst h).symm,
      fun h ↦ D.kd_snd_ne_x j (congrArg Prod.snd h)⟩ = D.kd j := by
    apply Dart.ext
    change (contractVertex x y y, contractVertex x y (D.kd j).snd) = (D.kd j).toProd
    rw [contractVertex_self, contractVertex_of_ne (D.kd_snd_ne_y j)]
    exact Prod.ext (D.kd_fst j).symm rfl
  have h' := (Equiv.symm_apply_eq D.equiv).2 h.symm
  unfold lift
  rw [h']

theorem lift_fst_of_lt {j : ℕ} (hj : j < D.k) : (D.lift j).fst = x :=
  congrArg Prod.fst (D.lift_toProd_of_lt hj)

theorem lift_fst_of_ge {j : ℕ} (hkj : D.k ≤ j) (hj : j < D.N) : (D.lift j).fst = y :=
  congrArg Prod.fst (D.lift_toProd_of_ge hkj hj)

theorem τ_apply (d : G.Dart) (hd : d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x)) :
    D.τ d = (D.equiv.symm (D.R'.rot (D.equiv ⟨d, hd⟩))).1 := by
  unfold τ
  exact Perm.ofSubtype_apply_of_mem (D.equiv.symm.permCongr D.R'.rot) hd

theorem τ_xy : D.τ D.xyDart = D.xyDart :=
  Perm.ofSubtype_apply_of_not_mem _ (by simp [xyDart])

theorem τ_yx : D.τ D.yxDart = D.yxDart :=
  Perm.ofSubtype_apply_of_not_mem _ (by simp [yxDart])

theorem equiv_lift (j : ℕ) : D.equiv ⟨D.lift j, D.lift_mem j⟩ = D.kd j := by
  have h : (⟨D.lift j, D.lift_mem j⟩ : UncontractDart G x y) = D.equiv.symm (D.kd j) := rfl
  rw [h, Equiv.apply_symm_apply]

theorem τ_lift_succ (j : ℕ) : D.τ (D.lift (j + 1)) = D.lift j := by
  rw [D.τ_apply _ (D.lift_mem (j + 1)), equiv_lift, rot_kd_succ]
  rfl

variable [Finite V]

omit [DecidableEq V] in
theorem N_pos : 0 < D.N := by
  have h := D.d₀.adj
  rw [D.hd₀] at h
  exact (Set.ncard_pos (Set.toFinite _)).2 ⟨_, h⟩

omit [DecidableEq V] [Finite V] in
theorem N_eq : D.N = ((contractEdge G x y).neighborSet D.d₀.fst).ncard := by
  rw [D.hd₀]

omit [DecidableEq V] in
theorem kd_add_N (j : ℕ) : D.kd (j + D.N) = D.kd j := by
  rw [kd, kd, pow_add, Perm.mul_apply, N_eq, RotationSystem.rot_inv_pow_ncard]

omit [DecidableEq V] in
theorem rot_kd_zero : D.R'.rot (D.kd 0) = D.kd (D.N - 1) := by
  have h := D.kd_add_N 0
  rw [zero_add] at h
  obtain ⟨M, hM⟩ : ∃ M, D.N = M + 1 := ⟨D.N - 1, by have := D.N_pos; omega⟩
  rw [← h, hM, rot_kd_succ, Nat.add_sub_cancel]

omit [DecidableEq V] in
theorem kd_injOn {i j : ℕ} (hi : i < D.N) (hj : j < D.N) (h : D.kd i = D.kd j) : i = j := by
  rw [N_eq, ← RotationSystem.minimalPeriod_rot_inv] at hi hj
  exact iterate_injOn_Iio_minimalPeriod hi hj (by simpa only [kd, coe_pow] using h)

omit [DecidableEq V] in
theorem exists_kd (e : (contractEdge G x y).Dart) (he : e.fst = x) : ∃ j < D.N, D.kd j = e := by
  have hadj : (contractEdge G x y).Adj D.d₀.fst e.snd := by
    have h := e.adj
    rw [show e.toProd.1 = D.d₀.fst from he.trans D.hd₀.symm] at h
    exact h
  obtain ⟨j, hj, hjs⟩ := D.R'.exists_rot_inv_pow_snd D.d₀ hadj
  rw [RotationSystem.minimalPeriod_rot_inv, ← N_eq] at hj
  exact ⟨j, hj, Dart.ext _ _ (Prod.ext ((D.kd_fst j).trans he.symm) hjs)⟩

theorem lift_injOn {i j : ℕ} (hi : i < D.N) (hj : j < D.N) (h : D.lift i = D.lift j) : i = j :=
  D.kd_injOn hi hj (D.equiv.symm.injective (Subtype.ext h))

theorem lift_N : D.lift D.N = D.lift 0 := by
  have h := D.kd_add_N 0
  rw [zero_add] at h
  unfold lift
  rw [h]

theorem τ_lift_zero : D.τ (D.lift 0) = D.lift (D.N - 1) := by
  rw [D.τ_apply _ (D.lift_mem 0), equiv_lift, rot_kd_zero]
  rfl

/-- The uncontracted rotation: `τ` times three conditional transpositions. `(lift 0, lift k)`
splits the cycle of `x` into two arcs, and the other two transpositions insert `xy` and `yx` at the
ends of the arcs. -/
noncomputable def rot : Perm G.Dart :=
  D.τ * cswap (0 < D.k ∧ D.k < D.N) (D.lift 0) (D.lift D.k) *
    cswap (0 < D.k) (D.lift 0) D.xyDart * cswap (D.k < D.N) (D.lift D.k) D.yxDart

omit [Finite V] in
theorem rot_apply (d : G.Dart) : D.rot d = D.τ (cswap (0 < D.k ∧ D.k < D.N) (D.lift 0) (D.lift D.k)
    (cswap (0 < D.k) (D.lift 0) D.xyDart (cswap (D.k < D.N) (D.lift D.k) D.yxDart d))) := rfl

theorem lift_ne_lift_zero {j : ℕ} (hj : j < D.N) (h0 : j ≠ 0) : D.lift j ≠ D.lift 0 :=
  fun h ↦ h0 (D.lift_injOn hj D.N_pos h)

theorem lift_ne_lift_k {j : ℕ} (hj : j < D.N) (hjk : j ≠ D.k) (h0 : j ≠ 0) :
    D.lift j ≠ D.lift D.k := by
  rcases D.k_le_N.lt_or_eq with hk | hk
  · exact fun h ↦ hjk (D.lift_injOn hj hk h)
  · rw [hk, lift_N]
    exact D.lift_ne_lift_zero hj h0

/-- Inside an arc: if `j ≠ 0, k`, then `rot (lift j) = lift (j - 1)`. -/
theorem rot_lift_of_ne {j : ℕ} (hj : j < D.N) (h0 : j ≠ 0) (hjk : j ≠ D.k) :
    D.rot (D.lift j) = D.lift (j - 1) := by
  have h1 := D.lift_ne_lift_zero hj h0
  have h2 := D.lift_ne_lift_k hj hjk h0
  rw [rot_apply, cswap_apply_of_ne _ h2 (D.lift_ne_yx j), cswap_apply_of_ne _ h1 (D.lift_ne_xy j),
    cswap_apply_of_ne _ h1 h2]
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [τ_lift_succ, Nat.add_sub_cancel]

/-- End of the `x`-arc: if `0 < k`, then `rot (lift 0) = xy`. -/
theorem rot_lift_zero (hk : 0 < D.k) : D.rot (D.lift 0) = D.xyDart := by
  have hxy0 : D.xyDart ≠ D.lift 0 := (D.lift_ne_xy 0).symm
  have hxyk : D.xyDart ≠ D.lift D.k := (D.lift_ne_xy D.k).symm
  by_cases hkN : D.k < D.N
  · have h1 : D.lift 0 ≠ D.lift D.k := fun h ↦ by
      have := D.lift_injOn D.N_pos hkN h
      omega
    rw [rot_apply, cswap_apply_of_ne _ h1 (D.lift_ne_yx 0), cswap_pos hk, swap_apply_left,
      cswap_apply_of_ne _ hxy0 hxyk, τ_xy]
  · rw [rot_apply, cswap_neg hkN, Perm.one_apply, cswap_pos hk, swap_apply_left,
      cswap_neg (fun h ↦ hkN h.2), Perm.one_apply, τ_xy]

/-- If `0 < k`, then `rot xy = lift (k - 1)`. -/
theorem rot_xy (hk : 0 < D.k) : D.rot D.xyDart = D.lift (D.k - 1) := by
  have hxyk : D.xyDart ≠ D.lift D.k := (D.lift_ne_xy D.k).symm
  rw [rot_apply, cswap_apply_of_ne _ hxyk D.xyDart_ne_yxDart, cswap_pos hk, swap_apply_right]
  by_cases hkN : D.k < D.N
  · rw [cswap_pos ⟨hk, hkN⟩, swap_apply_left]
    obtain ⟨i, hi⟩ : ∃ i, D.k = i + 1 := ⟨D.k - 1, by omega⟩
    rw [hi, τ_lift_succ, Nat.add_sub_cancel]
  · rw [cswap_neg (fun h ↦ hkN h.2), Perm.one_apply, τ_lift_zero]
    have : D.k = D.N := le_antisymm D.k_le_N (not_lt.1 hkN)
    rw [this]

omit [Finite V] in
/-- If `k = 0`, then `xy` is a fixed point (`x` is a leaf of `G`). -/
theorem rot_xy_of_eq_zero (hk : D.k = 0) : D.rot D.xyDart = D.xyDart := by
  have hxyk : D.xyDart ≠ D.lift D.k := (D.lift_ne_xy D.k).symm
  rw [rot_apply, cswap_apply_of_ne _ hxyk D.xyDart_ne_yxDart, cswap_neg (by omega),
    Perm.one_apply, cswap_neg (by omega), Perm.one_apply, τ_xy]

omit [Finite V] in
/-- End of the `y`-arc: if `k < N`, then `rot (lift k) = yx`. -/
theorem rot_lift_k (hkN : D.k < D.N) : D.rot (D.lift D.k) = D.yxDart := by
  have hyx0 : D.yxDart ≠ D.lift 0 := (D.lift_ne_yx 0).symm
  have hyxk : D.yxDart ≠ D.lift D.k := (D.lift_ne_yx D.k).symm
  rw [rot_apply, cswap_pos hkN, swap_apply_left, cswap_apply_of_ne _ hyx0 D.xyDart_ne_yxDart.symm,
    cswap_apply_of_ne _ hyx0 hyxk, τ_yx]

/-- If `k < N`, then `rot yx = lift (N - 1)`. -/
theorem rot_yx (hkN : D.k < D.N) : D.rot D.yxDart = D.lift (D.N - 1) := by
  rw [rot_apply, cswap_pos hkN, swap_apply_right]
  by_cases hk : 0 < D.k
  · have h1 : D.lift D.k ≠ D.lift 0 := fun h ↦ by
      have := D.lift_injOn hkN D.N_pos h
      omega
    rw [cswap_apply_of_ne _ h1 (D.lift_ne_xy D.k), cswap_pos ⟨hk, hkN⟩, swap_apply_right,
      τ_lift_zero]
  · have hk0 : D.k = 0 := by omega
    rw [cswap_neg hk, Perm.one_apply, cswap_neg (fun h ↦ hk h.1), Perm.one_apply, hk0,
      τ_lift_zero]

omit [Finite V] in
/-- If `k = N`, then `yx` is a fixed point (`y` is a leaf of `G`). -/
theorem rot_yx_of_eq (hk : D.k = D.N) : D.rot D.yxDart = D.yxDart := by
  have hyx0 : D.yxDart ≠ D.lift 0 := (D.lift_ne_yx 0).symm
  have hyxk : D.yxDart ≠ D.lift D.k := (D.lift_ne_yx D.k).symm
  rw [rot_apply, cswap_neg (c := D.k < D.N) (by omega), Perm.one_apply,
    cswap_apply_of_ne _ hyx0 D.xyDart_ne_yxDart.symm, cswap_apply_of_ne _ hyx0 hyxk, τ_yx]


/-! ### Rotation system conditions -/

omit [Finite V] in
theorem equiv_fst (s : UncontractDart G x y) : (D.equiv s).fst = contractVertex x y s.1.fst := rfl

omit [Finite V] in
/-- A dart of `G/xy` whose start vertex is not `x` corresponds to a dart with the same start
vertex. -/
theorem equiv_symm_fst_of_ne (e : (contractEdge G x y).Dart) (he : e.fst ≠ x) :
    (D.equiv.symm e).1.fst = e.fst := by
  have h : contractVertex x y (D.equiv.symm e).1.fst = e.fst := by
    rw [← equiv_fst, Equiv.apply_symm_apply]
  have hy : (D.equiv.symm e).1.fst ≠ y := fun hy ↦ he (by rw [← h, hy, contractVertex_self])
  rwa [contractVertex_of_ne hy] at h

omit [DecidableEq V] [Finite V] in
theorem fst_rot_pow' (e : (contractEdge G x y).Dart) (n : ℕ) :
    ((D.R'.rot ^ n) e).fst = e.fst := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, D.R'.fst_rot, ih]

omit [DecidableEq V] [Finite V] in
theorem mem_of_fst_ne {d : G.Dart} (hx : d.fst ≠ x) (hy : d.fst ≠ y) :
    d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x) :=
  ⟨fun h ↦ hx (congrArg Prod.fst h), fun h ↦ hy (congrArg Prod.fst h)⟩

omit [Finite V] in
theorem τ_fst_of_ne (d : G.Dart) (hx : d.fst ≠ x) (hy : d.fst ≠ y) : (D.τ d).fst = d.fst := by
  rw [D.τ_apply d (mem_of_fst_ne hx hy)]
  have he : (D.equiv ⟨d, mem_of_fst_ne hx hy⟩).fst = d.fst := by
    rw [equiv_fst, contractVertex_of_ne hy]
  rw [D.equiv_symm_fst_of_ne _ (by rw [D.R'.fst_rot, he]; exact hx), D.R'.fst_rot, he]

omit [Finite V] in
/-- If the start vertex is neither `x` nor `y`, then `rot = τ`. -/
theorem rot_of_fst_ne (d : G.Dart) (hx : d.fst ≠ x) (hy : d.fst ≠ y) : D.rot d = D.τ d := by
  have hl : ∀ j, d ≠ D.lift j := fun j h ↦ (D.lift_fst_mem j).elim
    (fun h' ↦ hx (by rw [h]; exact h')) (fun h' ↦ hy (by rw [h]; exact h'))
  have hxy : d ≠ D.xyDart := fun h ↦ hx (by rw [h]; rfl)
  have hyx : d ≠ D.yxDart := fun h ↦ hy (by rw [h]; rfl)
  rw [rot_apply, cswap_apply_of_ne _ (hl D.k) hyx, cswap_apply_of_ne _ (hl 0) hxy,
    cswap_apply_of_ne _ (hl 0) (hl D.k)]

theorem fst_rot (d : G.Dart) : (D.rot d).fst = d.fst := by
  by_cases hxy : d = D.xyDart
  · rw [hxy]
    by_cases hk : D.k = 0
    · rw [D.rot_xy_of_eq_zero hk]
    · rw [D.rot_xy (by omega)]
      exact D.lift_fst_of_lt (by omega)
  by_cases hyx : d = D.yxDart
  · rw [hyx]
    by_cases hk : D.k = D.N
    · rw [D.rot_yx_of_eq hk]
    · have hkN : D.k < D.N := lt_of_le_of_ne D.k_le_N hk
      rw [D.rot_yx hkN]
      exact D.lift_fst_of_ge (by omega) (by have := D.N_pos; omega)
  have hd : d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x) :=
    ⟨fun h ↦ hxy (Dart.ext _ _ h), fun h ↦ hyx (Dart.ext _ _ h)⟩
  by_cases he : (D.equiv ⟨d, hd⟩).fst = x
  · obtain ⟨j, hj, hje⟩ := D.exists_kd _ he
    have hdj : d = D.lift j := by
      unfold lift
      rw [hje, Equiv.symm_apply_apply]
    rw [hdj]
    by_cases hjk : j = D.k
    · subst hjk
      rw [D.rot_lift_k hj]
      exact (D.lift_fst_of_ge le_rfl hj).symm
    by_cases hj0 : j = 0
    · subst hj0
      have hk : 0 < D.k := by omega
      rw [D.rot_lift_zero hk]
      exact (D.lift_fst_of_lt hk).symm
    rw [D.rot_lift_of_ne hj hj0 hjk]
    rcases lt_or_gt_of_ne hjk with h | h
    · rw [D.lift_fst_of_lt h, D.lift_fst_of_lt (by omega)]
    · rw [D.lift_fst_of_ge (by omega) hj, D.lift_fst_of_ge (by omega) (by omega)]
  · have hx : d.fst ≠ x := fun h ↦ he (by rw [equiv_fst, h, contractVertex_of_ne D.hxy.ne])
    have hy : d.fst ≠ y := fun h ↦ he (by rw [equiv_fst, h, contractVertex_self])
    rw [D.rot_of_fst_ne d hx hy, D.τ_fst_of_ne d hx hy]

theorem rot_pow_xy : ∀ i, i < D.k → (D.rot ^ (i + 1)) D.xyDart = D.lift (D.k - 1 - i) := by
  intro i
  induction i with
  | zero => intro hk; rw [zero_add, pow_one, D.rot_xy (by omega), Nat.sub_zero]
  | succ i ih =>
    intro hi
    rw [pow_succ', Perm.mul_apply, ih (by omega),
      D.rot_lift_of_ne (by have := D.k_le_N; omega) (by omega) (by omega)]
    congr 1

theorem rot_pow_yx : ∀ i, i < D.N - D.k → (D.rot ^ (i + 1)) D.yxDart = D.lift (D.N - 1 - i) := by
  intro i
  induction i with
  | zero => intro hk; rw [zero_add, pow_one, D.rot_yx (by omega), Nat.sub_zero]
  | succ i ih =>
    intro hi
    rw [pow_succ', Perm.mul_apply, ih (by omega), D.rot_lift_of_ne (by omega) (by omega) (by omega)]
    congr 1

/-- An old dart starting at `x` is enumerated as some `lift j`. -/
theorem lift_of_fst_x {d : G.Dart} (hd : d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x)) (hx : d.fst = x) :
    ∃ j < D.N, d = D.lift j := by
  have he : (D.equiv ⟨d, hd⟩).fst = x := by rw [equiv_fst, hx, contractVertex_of_ne D.hxy.ne]
  obtain ⟨j, hj, hje⟩ := D.exists_kd _ he
  refine ⟨j, hj, ?_⟩
  unfold lift
  rw [hje, Equiv.symm_apply_apply]

theorem lift_of_fst_y {d : G.Dart} (hd : d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x)) (hy : d.fst = y) :
    ∃ j < D.N, d = D.lift j := by
  have he : (D.equiv ⟨d, hd⟩).fst = x := by rw [equiv_fst, hy, contractVertex_self]
  obtain ⟨j, hj, hje⟩ := D.exists_kd _ he
  refine ⟨j, hj, ?_⟩
  unfold lift
  rw [hje, Equiv.symm_apply_apply]

theorem sameCycle_xy (d : G.Dart) (hd : d.fst = x) : D.rot.SameCycle D.xyDart d := by
  by_cases hxy : d = D.xyDart
  · rw [hxy]
  have hyx : d ≠ D.yxDart := fun h ↦ D.hxy.ne (hd.symm.trans (by rw [h]; rfl))
  obtain ⟨j, hj, rfl⟩ := D.lift_of_fst_x
    ⟨fun h ↦ hxy (Dart.ext _ _ h), fun h ↦ hyx (Dart.ext _ _ h)⟩ hd
  have hjk : j < D.k := by
    by_contra h
    exact D.hxy.ne (hd.symm.trans (D.lift_fst_of_ge (not_lt.1 h) hj))
  refine ⟨((D.k - 1 - j + 1 : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, D.rot_pow_xy _ (by omega)]
  congr 1
  omega

theorem sameCycle_yx (d : G.Dart) (hd : d.fst = y) : D.rot.SameCycle D.yxDart d := by
  by_cases hyx : d = D.yxDart
  · rw [hyx]
  have hxy : d ≠ D.xyDart := fun h ↦ D.hxy.ne ((by rw [h]; rfl : x = d.fst).trans hd)
  obtain ⟨j, hj, rfl⟩ := D.lift_of_fst_y
    ⟨fun h ↦ hxy (Dart.ext _ _ h), fun h ↦ hyx (Dart.ext _ _ h)⟩ hd
  have hkj : D.k ≤ j := by
    by_contra h
    exact D.hxy.ne ((D.lift_fst_of_lt (not_le.1 h)).symm.trans hd)
  refine ⟨((D.N - 1 - j + 1 : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, D.rot_pow_yx _ (by omega)]
  congr 1
  omega

omit [Finite V] in
theorem rot_pow_of_fst_ne (d : G.Dart) (hx : d.fst ≠ x) (hy : d.fst ≠ y) (n : ℕ) :
    (D.rot ^ n) d =
      (D.equiv.symm ((D.R'.rot ^ n) (D.equiv ⟨d, mem_of_fst_ne hx hy⟩))).1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    set e := D.equiv ⟨d, mem_of_fst_ne hx hy⟩ with he_def
    have he : e.fst = d.fst := by rw [he_def, equiv_fst, contractVertex_of_ne hy]
    have hs : (D.equiv.symm ((D.R'.rot ^ n) e)).1.fst = d.fst := by
      rw [D.equiv_symm_fst_of_ne _ (by rw [D.fst_rot_pow', he]; exact hx), D.fst_rot_pow', he]
    rw [pow_succ', Perm.mul_apply, ih, D.rot_of_fst_ne _ (hs ▸ hx) (hs ▸ hy),
      D.τ_apply _ (D.equiv.symm ((D.R'.rot ^ n) e)).2, pow_succ', Perm.mul_apply]
    simp

theorem sameCycle_rot (d d' : G.Dart) (h : d.fst = d'.fst) : D.rot.SameCycle d d' := by
  by_cases hx : d.fst = x
  · exact (D.sameCycle_xy d hx).symm.trans (D.sameCycle_xy d' (h ▸ hx))
  by_cases hy : d.fst = y
  · exact (D.sameCycle_yx d hy).symm.trans (D.sameCycle_yx d' (h ▸ hy))
  have hx' : d'.fst ≠ x := h ▸ hx
  have hy' : d'.fst ≠ y := h ▸ hy
  have hfst : (D.equiv ⟨d, mem_of_fst_ne hx hy⟩).fst =
      (D.equiv ⟨d', mem_of_fst_ne hx' hy'⟩).fst := by
    rw [equiv_fst, equiv_fst, contractVertex_of_ne hy, contractVertex_of_ne hy', h]
  obtain ⟨n, hn⟩ := (D.R'.sameCycle_rot _ _ hfst).exists_nat_pow_eq
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast, D.rot_pow_of_fst_ne d hx hy, hn, Equiv.symm_apply_apply]

/-- The uncontracted rotation system. -/
noncomputable def rotationSystem : RotationSystem G where
  rot := D.rot
  fst_rot := D.fst_rot
  sameCycle_rot := D.sameCycle_rot


/-! ### Number of face cycles -/

/-- Dart reversal. -/
def rev (_ : UncontractData G x y) : Perm G.Dart :=
  Function.Involutive.toPerm _ Dart.symm_involutive

omit [DecidableEq V] [Finite V] in
theorem rev_involutive : Involutive D.rev := Dart.symm_involutive

omit [DecidableEq V] [Finite V] in
theorem rev_xy : D.rev D.xyDart = D.yxDart := rfl

omit [DecidableEq V] [Finite V] in
theorem rev_yx : D.rev D.yxDart = D.xyDart := rfl

theorem facePerm_eq : D.rotationSystem.facePerm = D.rot * D.rev :=
  Equiv.ext fun _ ↦ rfl

omit [DecidableEq V] [Finite V] in
theorem rev_mem {d : G.Dart} (hd : d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x)) :
    (D.rev d).toProd ≠ (x, y) ∧ (D.rev d).toProd ≠ (y, x) :=
  ⟨fun h ↦ hd.2 (by
      have h' : d.toProd.swap = (x, y) := h
      simpa using congrArg Prod.swap h'),
    fun h ↦ hd.1 (by
      have h' : d.toProd.swap = (y, x) := h
      simpa using congrArg Prod.swap h')⟩

omit [DecidableEq V] [Finite V] in
theorem ne_xy_of_mem {d : G.Dart} (hd : d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x)) : d ≠ D.xyDart :=
  fun h ↦ hd.1 (by rw [h]; rfl)

omit [DecidableEq V] [Finite V] in
theorem ne_yx_of_mem {d : G.Dart} (hd : d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x)) : d ≠ D.yxDart :=
  fun h ↦ hd.2 (by rw [h]; rfl)

omit [Finite V] in
theorem τ_rev_xy : (D.τ * D.rev) D.xyDart = D.yxDart := by
  rw [Perm.mul_apply, rev_xy, τ_yx]

omit [Finite V] in
theorem τ_rev_yx : (D.τ * D.rev) D.yxDart = D.xyDart := by
  rw [Perm.mul_apply, rev_yx, τ_xy]

/-- Removing the 2-cycle of `xy` and `yx` from `τ ∘ σ` leaves the transported `φ'`. -/
theorem orbitCount_τ_rev : orbitCount (D.τ * D.rev) = orbitCount D.R'.facePerm + 1 := by
  set g := D.τ * D.rev * swap D.xyDart D.yxDart with hg
  have hgxy : g D.xyDart = D.xyDart := by
    rw [hg, Perm.mul_apply, swap_apply_left, τ_rev_yx]
  have hgyx : g D.yxDart = D.yxDart := by
    rw [hg, Perm.mul_apply, swap_apply_right, τ_rev_xy]
  have hgd : ∀ d (hd : d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x)),
      g d = (D.equiv.symm (D.R'.facePerm (D.equiv ⟨d, hd⟩))).1 := by
    intro d hd
    rw [hg, Perm.mul_apply, swap_apply_of_ne_of_ne (D.ne_xy_of_mem hd) (D.ne_yx_of_mem hd),
      Perm.mul_apply, D.τ_apply _ (D.rev_mem hd)]
    rfl
  have hP : ∀ d, (g d).toProd ≠ (x, y) ∧ (g d).toProd ≠ (y, x) ↔
      d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x) := by
    intro d
    constructor
    · intro h
      refine ⟨fun h' ↦ h.1 ?_, fun h' ↦ h.2 ?_⟩
      · rw [show d = D.xyDart from Dart.ext _ _ h', hgxy]; rfl
      · rw [show d = D.yxDart from Dart.ext _ _ h', hgyx]; rfl
    · intro hd
      rw [hgd d hd]
      exact (D.equiv.symm _).2
  have h1 := orbitCount_eq_subtypePerm_add g
    (fun d : G.Dart ↦ d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x)) hP (by
    intro d hd
    by_cases h : d.toProd = (x, y)
    · rw [show d = D.xyDart from Dart.ext _ _ h, hgxy]
    · have h' : d.toProd = (y, x) := by
        by_contra h'
        exact hd ⟨h, h'⟩
      rw [show d = D.yxDart from Dart.ext _ _ h', hgyx])
  have h2 : g.subtypePerm hP = D.equiv.symm.permCongr D.R'.facePerm :=
    Equiv.ext fun s ↦ Subtype.ext (by
      change g s.1 = _
      rw [hgd s.1 s.2]
      rfl)
  have h3 : Nat.card {d : G.Dart // ¬ (d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x))} = 2 := by
    have hs : {d : G.Dart | ¬ (d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x))} = {D.xyDart, D.yxDart} := by
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_and_or,
        not_not]
      constructor
      · rintro (h | h)
        · exact Or.inl (Dart.ext _ _ h)
        · exact Or.inr (Dart.ext _ _ h)
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
    change Nat.card ↥{d : G.Dart | ¬ (d.toProd ≠ (x, y) ∧ d.toProd ≠ (y, x))} = 2
    rw [Nat.card_coe_set_eq, hs, Set.ncard_pair D.xyDart_ne_yxDart]
  have h4 : orbitCount (g * swap D.xyDart D.yxDart) + 1 = orbitCount g :=
    orbitCount_mul_swap_of_not_sameCycle fun h ↦ D.xyDart_ne_yxDart (h.eq_of_left hgxy)
  have h5 : g * swap D.xyDart D.yxDart = D.τ * D.rev := by
    rw [hg, mul_assoc, swap_mul_self, mul_one]
  rw [h2, orbitCount_permCongr, h3] at h1
  rw [h5] at h4
  omega

/-- Face count of blueprint `lem:uncontract`: undoing the contraction preserves the number of
face cycles. -/
theorem orbitCount_facePerm : orbitCount D.rotationSystem.facePerm = orbitCount D.R'.facePerm := by
  have hτ := D.orbitCount_τ_rev
  have hface : D.rot * D.rev = D.τ * D.rev *
      cswap (0 < D.k ∧ D.k < D.N) (D.rev (D.lift 0)) (D.rev (D.lift D.k)) *
      cswap (0 < D.k) (D.rev (D.lift 0)) D.yxDart *
        cswap (D.k < D.N) (D.rev (D.lift D.k)) D.xyDart := by
    have hσ := D.rev_involutive
    rw [rot, mul_cswap_mul_involutive _ D.rev hσ, mul_cswap_mul_involutive _ D.rev hσ,
      mul_cswap_mul_involutive _ D.rev hσ, rev_xy, rev_yx]
  have hu := D.rev_mem (D.lift_mem 0)
  have hw := D.rev_mem (D.lift_mem D.k)
  rw [facePerm_eq, hface]
  by_cases hk0 : 0 < D.k
  · by_cases hkN : D.k < D.N
    · have huw : D.rev (D.lift 0) ≠ D.rev (D.lift D.k) := fun h ↦ by
        have := D.lift_injOn D.N_pos hkN (D.rev_involutive.injective h)
        omega
      rw [cswap_pos ⟨hk0, hkN⟩, cswap_pos hk0, cswap_pos hkN]
      have := orbitCount_three_swaps (D.τ * D.rev) D.τ_rev_xy D.τ_rev_yx (D.ne_xy_of_mem hu)
        (D.ne_yx_of_mem hu) (D.ne_xy_of_mem hw) (D.ne_yx_of_mem hw) huw
      omega
    · rw [cswap_neg (fun h ↦ hkN h.2), cswap_pos hk0, cswap_neg hkN, mul_one, mul_one]
      have := orbitCount_mul_swap_two_cycle (D.τ * D.rev) D.τ_rev_xy D.τ_rev_yx (D.ne_xy_of_mem hu)
        (D.ne_yx_of_mem hu)
      omega
  · have hkN : D.k < D.N := by have := D.N_pos; omega
    rw [cswap_neg (fun h ↦ hk0 h.1), cswap_neg hk0, cswap_pos hkN, mul_one, mul_one]
    have := orbitCount_mul_swap_two_cycle (D.τ * D.rev) D.τ_rev_yx D.τ_rev_xy (D.ne_yx_of_mem hw)
      (D.ne_xy_of_mem hw)
    omega


/-! ### Counts and genus -/

include D in
omit [DecidableEq V] [Finite V] in
theorem not_isIsolated_x : ¬ (contractEdge G x y).IsIsolated x := fun h ↦
  h D.d₀.snd (by have h' := D.d₀.adj; rw [D.hd₀] at h'; exact h')

/-- The bijection between the darts other than the reverse pair `xy`, `yx` and the darts of
`G/xy` (the form used for edge counting with a deleted pair). -/
noncomputable def equivDeletePair :
    {d : G.Dart // d ≠ D.xyDart ∧ d ≠ D.xyDart.symm} ≃ (contractEdge G x y).Dart :=
  (Equiv.subtypeEquivRight fun d ↦ by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h ↦ h1 (Dart.ext _ _ h), fun h ↦ h2 (Dart.ext _ _ h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h ↦ h1 (by rw [h]; rfl), fun h ↦ h2 (by rw [h]; rfl)⟩).trans D.equiv

include D in
theorem ncard_edgeSet : G.edgeSet.ncard = (contractEdge G x y).edgeSet.ncard + 1 :=
  ncard_edgeSet_of_dartEquiv_delete_pair D.xyDart D.equivDeletePair

/-- Undoing the contraction decreases the Euler characteristic by 2. -/
theorem eulerChar_rotationSystem : D.rotationSystem.eulerChar + 2 = D.R'.eulerChar := by
  have hO := D.orbitCount_facePerm
  have hE := D.ncard_edgeSet
  have hI := ncard_isolated_contractEdge D.hxy D.not_isIsolated_x
  unfold RotationSystem.eulerChar RotationSystem.numFaces
  rw [hO, hE, hI]
  push_cast
  omega

/-- Blueprint `lem:uncontract`: if `R'` has genus 0, so does the uncontracted rotation
system. -/
theorem eulerChar_eq (hR' : D.R'.eulerChar = 2 * Nat.card (contractEdge G x y).ConnectedComponent) :
    D.rotationSystem.eulerChar = 2 * Nat.card G.ConnectedComponent := by
  have h := D.eulerChar_rotationSystem
  have hc := card_connectedComponent_contractEdge D.hxy
  rw [hR', hc] at h
  push_cast at h
  omega

/-! ### Public rotation formulas (dart bijection and `toProd`) -/

theorem rotationSystem_rot (d : G.Dart) : D.rotationSystem.rot d = D.rot d := rfl

/-- If `0 < k`, the successor of `(x, y)` is `(x, u_{k-1})`. -/
theorem rotationSystem_rot_xy (hk : 0 < D.k) :
    (D.rotationSystem.rot D.xyDart).toProd = (x, (D.kd (D.k - 1)).snd) := by
  rw [rotationSystem_rot, D.rot_xy hk, D.lift_toProd_of_lt (by omega)]

/-- If `0 < k`, the successor of `(x, u_0)` is `(x, y)`. -/
theorem rotationSystem_rot_to_xy (hk : 0 < D.k) (d : G.Dart) (hd : d.toProd = (x, (D.kd 0).snd)) :
    D.rotationSystem.rot d = D.xyDart := by
  have h : d = D.lift 0 := Dart.ext _ _ (hd.trans (D.lift_toProd_of_lt hk).symm)
  rw [rotationSystem_rot, h, D.rot_lift_zero hk]

/-- If `k < N`, the successor of `(y, x)` is `(y, u_{N-1})`. -/
theorem rotationSystem_rot_yx (hk : D.k < D.N) :
    (D.rotationSystem.rot D.yxDart).toProd = (y, (D.kd (D.N - 1)).snd) := by
  rw [rotationSystem_rot, D.rot_yx hk, D.lift_toProd_of_ge (by omega) (by omega)]

/-- If `k < N`, the successor of `(y, u_k)` is `(y, x)`. -/
theorem rotationSystem_rot_to_yx (hk : D.k < D.N) (d : G.Dart)
    (hd : d.toProd = (y, (D.kd D.k).snd)) : D.rotationSystem.rot d = D.yxDart := by
  have h : d = D.lift D.k := Dart.ext _ _ (hd.trans (D.lift_toProd_of_ge le_rfl hk).symm)
  rw [rotationSystem_rot, h, D.rot_lift_k hk]

/-- If `k = 0`, then `(x, y)` is a fixed point. -/
theorem rotationSystem_rot_xy_of_eq_zero (hk : D.k = 0) :
    D.rotationSystem.rot D.xyDart = D.xyDart := D.rot_xy_of_eq_zero hk

/-- If `k = N`, then `(y, x)` is a fixed point. -/
theorem rotationSystem_rot_yx_of_eq (hk : D.k = D.N) :
    D.rotationSystem.rot D.yxDart = D.yxDart := D.rot_yx_of_eq hk

/-- Inside an arc (`j ≠ 0, k`), the successor of `u_j` is `u_{j-1}`. -/
theorem rotationSystem_rot_lift {j : ℕ} (hj : j < D.N) (h0 : j ≠ 0) (hjk : j ≠ D.k) :
    D.rotationSystem.rot (D.lift j) = D.lift (j - 1) := D.rot_lift_of_ne hj h0 hjk

/-- At vertices other than `x` and `y`, the rotation is `ρ'` transported along the dart
bijection. -/
theorem equiv_rotationSystem_rot (d : G.Dart) (hx : d.fst ≠ x) (hy : d.fst ≠ y) :
    D.equiv ⟨D.rotationSystem.rot d, mem_of_fst_ne (by rw [rotationSystem_rot, D.fst_rot]; exact hx)
      (by rw [rotationSystem_rot, D.fst_rot]; exact hy)⟩ =
      D.R'.rot (D.equiv ⟨d, mem_of_fst_ne hx hy⟩) := by
  have hval : D.rotationSystem.rot d =
      (D.equiv.symm (D.R'.rot (D.equiv ⟨d, mem_of_fst_ne hx hy⟩))).1 := by
    rw [rotationSystem_rot, D.rot_of_fst_ne d hx hy, D.τ_apply]
  have h : (⟨D.rotationSystem.rot d, mem_of_fst_ne (by rw [rotationSystem_rot, D.fst_rot]; exact hx)
      (by rw [rotationSystem_rot, D.fst_rot]; exact hy)⟩ : UncontractDart G x y) =
      D.equiv.symm (D.R'.rot (D.equiv ⟨d, mem_of_fst_ne hx hy⟩)) := Subtype.ext hval
  rw [h, Equiv.apply_symm_apply]

end UncontractData

/-- Blueprint `lem:uncontract`. Let `xy` be an edge without common neighbors and `R'` a rotation
system of `G/xy`, and classify the neighbors of `x` in `G/xy` by adjacency in `G`. If, around `x`,
they split into an `x`-arc of neighbors of `x` in `G` (`j < k`) and a `y`-arc of neighbors of `y`
in `G` (`k ≤ j < N`), there is a rotation system of `G` with the same number of face cycles, and
it has genus 0 if `R'` does. The rotation formulas are the `rotationSystem_rot_*` lemmas of
`UncontractData`. -/
theorem RotationSystem.exists_uncontract [Finite V] (hxy : G.Adj x y)
    (hcommon : ∀ z, ¬ (G.Adj x z ∧ G.Adj y z)) (R' : RotationSystem (contractEdge G x y))
    (d₀ : (contractEdge G x y).Dart) (hd₀ : d₀.fst = x) (k : ℕ)
    (hk : k ≤ ((contractEdge G x y).neighborSet x).ncard)
    (hA : ∀ j < k, G.Adj x ((R'.rot⁻¹ ^ j) d₀).snd)
    (hY : ∀ j, k ≤ j → j < ((contractEdge G x y).neighborSet x).ncard →
      G.Adj y ((R'.rot⁻¹ ^ j) d₀).snd) :
    ∃ R : RotationSystem G, orbitCount R.facePerm = orbitCount R'.facePerm ∧
      (R'.eulerChar = 2 * Nat.card (contractEdge G x y).ConnectedComponent →
        R.eulerChar = 2 * Nat.card G.ConnectedComponent) :=
  let D : UncontractData G x y := ⟨hxy, hcommon, R', d₀, hd₀, k, hk, hA, hY⟩
  ⟨D.rotationSystem, D.orbitCount_facePerm, D.eulerChar_eq⟩

end Kuratowski
