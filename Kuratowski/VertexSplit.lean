import Kuratowski.AddEdge
import Kuratowski.Small
import Kuratowski.Sum
import Kuratowski.Uncontract

/-!
# 구간 조건이면 꼭짓점을 나눠도 평면 (블루프린트 `lem:S`)

`x ∼ y`이고 `G/xy`의 종수 0 회전 체계 `R'`에서 `x` 둘레의 이웃 단어가 `B? X* B? Y*` 꼴이면 `G`는 평면이다.
Lean 진술의 구간 조건 `IntervalWord`는 보조정리 `lem:J2`와 같은 역회전(`ρ'⁻¹`) 순서로 읽는다.

* 빈 단어: `x`, `y`의 이웃은 서로뿐이라 `G = G/xy ⊔ edge x y`이고 두 지지 집합이 서로소다.
* 비지 않은 단어: 공통 이웃은 `x`쪽 호의 양 끝 `b₂ = u_0`, `b₁ = u_{k-1}`에만 있다.
  공통 이웃 변 `yb`를 모두 지운 `G₀ = dropCommon G x y`는 `G₀/xy = G/xy`이고 공통 이웃이 없다.
  `lem:uncontract`로 `G₀`의 종수 0 회전 체계를 얻고, `lem:add_edge`로 `yb₁`, `yb₂`를 차례로 넣는다.
-/

namespace Kuratowski

open SimpleGraph Equiv Equiv.Perm Function

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}

/-- 블루프린트 `lem:S`의 구간 조건. 빈 단어이거나, `x`에서 나가는 `G/xy`의 다트 `d₀`와 `k ≤ N`이 있어
`u_j = (ρ'⁻¹^j d₀).snd`가 `j < k`이면 `G`에서 `x`의 이웃(`X`/`B`), `k ≤ j < N`이면 `x`의 이웃이 아니며(`Y`),
`0 < j`, `j + 1 < k`이면 `y`의 이웃이 아니다(`B`는 `x`쪽 호의 양 끝에만). -/
def IntervalWord (G : SimpleGraph V) (x y : V) (R' : RotationSystem (contractEdge G x y)) : Prop :=
  (contractEdge G x y).neighborSet x = ∅ ∨
    ∃ d₀ : (contractEdge G x y).Dart, d₀.fst = x ∧
      ∃ k ≤ ((contractEdge G x y).neighborSet x).ncard,
        (∀ j < k, G.Adj x ((R'.rot⁻¹ ^ j) d₀).snd) ∧
        (∀ j, k ≤ j → j < ((contractEdge G x y).neighborSet x).ncard →
          ¬ G.Adj x ((R'.rot⁻¹ ^ j) d₀).snd) ∧
        (∀ j, 0 < j → j + 1 < k → ¬ G.Adj y ((R'.rot⁻¹ ^ j) d₀).snd)

/-! ### 빈 단어 -/

/-- 빈 단어: `G/xy`에서 `x`가 고립이면 `G = G/xy ⊔ edge x y`이고 두 지지 집합은 서로소다. -/
theorem isPlanar_of_contractEdge_of_isolated [Finite V] (hxy : G.Adj x y)
    (hP : IsPlanar (contractEdge G x y)) (h0 : (contractEdge G x y).neighborSet x = ∅) :
    IsPlanar G := by
  have hx : ∀ z, G.Adj x z → z = y := by
    intro z hz
    by_contra hzy
    have h : z ∈ (contractEdge G x y).neighborSet x :=
      (contractEdge_adj_left hxy.ne).2 ⟨hz.ne.symm, hzy, Or.inl hz⟩
    rw [h0] at h
    exact h
  have hy : ∀ z, G.Adj y z → z = x := by
    intro z hz
    by_contra hzx
    have h : z ∈ (contractEdge G x y).neighborSet x :=
      (contractEdge_adj_left hxy.ne).2 ⟨hzx, hz.ne.symm, Or.inr hz⟩
    rw [h0] at h
    exact h
  have hle : G ≤ contractEdge G x y ⊔ edge x y := by
    intro p q h
    by_cases hpq : (p = x ∧ q = y) ∨ (p = y ∧ q = x)
    · exact Or.inr ((edge_adj _ _ _ _).2 ⟨hpq, h.ne⟩)
    · left
      have hp : p ≠ y := fun hp ↦ hpq (Or.inr ⟨hp, hy q (by rw [← hp]; exact h)⟩)
      have hq : q ≠ y := fun hq ↦ hpq (Or.inl ⟨hy p (by rw [← hq]; exact h.symm), hq⟩)
      exact ⟨h.ne, hp, hq, Or.inl h⟩
  have hsupp : (edge x y).support ⊆ {x, y} := by
    intro w hw
    obtain ⟨z, hz⟩ := (mem_support _).1 hw
    rcases ((edge_adj _ _ _ _).1 hz).1 with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hd : Disjoint (contractEdge G x y).support (edge x y).support := by
    rw [Set.disjoint_left]
    intro w hwK hwE
    obtain ⟨z, hz⟩ := (mem_support _).1 hwK
    rcases hsupp hwE with h | h
    · rw [h] at hz
      have hz' : z ∈ (contractEdge G x y).neighborSet x := hz
      rw [h0] at hz'
      exact hz'
    · rw [Set.mem_singleton_iff] at h
      exact isIsolated_contractEdge (G := G) (x := x) z (h ▸ hz)
  have hE : IsPlanar (edge x y) := isPlanar_of_ncard_support_le_four _ (by
    have h1 := Set.ncard_le_ncard hsupp (Set.toFinite _)
    have h2 := Set.ncard_insert_le x ({y} : Set V)
    rw [Set.ncard_singleton] at h2
    omega)
  exact (hP.sup_of_disjoint hE hd).mono hle

/-! ### 공통 이웃 변 지우기 -/

/-- `x`, `y`의 공통 이웃 `z`마다 변 `yz`를 지운 그래프. -/
def dropCommon (G : SimpleGraph V) (x y : V) : SimpleGraph V :=
  G.deleteEdges {e | ∃ z, G.Adj x z ∧ G.Adj y z ∧ e = s(y, z)}

omit [DecidableEq V] in
theorem dropCommon_adj {p q : V} : (dropCommon G x y).Adj p q ↔
    G.Adj p q ∧ ¬ ((p = y ∧ G.Adj x q ∧ G.Adj y q) ∨ (q = y ∧ G.Adj x p ∧ G.Adj y p)) := by
  rw [dropCommon, deleteEdges_adj]
  apply and_congr_right
  intro _
  apply not_congr
  constructor
  · rintro ⟨z, hxz, hyz, h⟩
    rcases Sym2.eq_iff.1 h with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact Or.inl ⟨hp, by rw [hq]; exact hxz, by rw [hq]; exact hyz⟩
    · exact Or.inr ⟨hq, by rw [hp]; exact hxz, by rw [hp]; exact hyz⟩
  · rintro (⟨hp, hxq, hyq⟩ | ⟨hq, hxp, hyp⟩)
    · exact ⟨q, hxq, hyq, by rw [hp]⟩
    · exact ⟨p, hxp, hyp, by rw [hq, Sym2.eq_swap]⟩

omit [DecidableEq V] in
theorem dropCommon_le : dropCommon G x y ≤ G := fun _ _ h ↦ (dropCommon_adj.1 h).1

omit [DecidableEq V] in
theorem dropCommon_adj_of_ne {p q : V} (hp : p ≠ y) (hq : q ≠ y) :
    (dropCommon G x y).Adj p q ↔ G.Adj p q := by
  rw [dropCommon_adj]
  constructor
  · exact fun h ↦ h.1
  · intro h
    refine ⟨h, ?_⟩
    rintro (⟨h', -⟩ | ⟨h', -⟩)
    · exact hp h'
    · exact hq h'

omit [DecidableEq V] in
theorem dropCommon_adj_x (hxy : x ≠ y) {q : V} : (dropCommon G x y).Adj x q ↔ G.Adj x q := by
  rw [dropCommon_adj]
  constructor
  · exact fun h ↦ h.1
  · intro h
    refine ⟨h, ?_⟩
    rintro (⟨h', -⟩ | ⟨-, h', -⟩)
    · exact hxy h'
    · exact G.loopless.irrefl x h'

omit [DecidableEq V] in
theorem dropCommon_adj_y {q : V} : (dropCommon G x y).Adj y q ↔ G.Adj y q ∧ ¬ G.Adj x q := by
  rw [dropCommon_adj]
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨h, fun hxq ↦ hn (Or.inl ⟨rfl, hxq, h⟩)⟩
  · rintro ⟨h, hn⟩
    refine ⟨h, ?_⟩
    rintro (⟨-, h', -⟩ | ⟨-, -, h'⟩)
    · exact hn h'
    · exact G.loopless.irrefl y h'

omit [DecidableEq V] in
theorem dropCommon_no_common (hxy : x ≠ y) (z : V) :
    ¬ ((dropCommon G x y).Adj x z ∧ (dropCommon G x y).Adj y z) := by
  rintro ⟨h1, h2⟩
  exact (dropCommon_adj_y.1 h2).2 ((dropCommon_adj_x hxy).1 h1)

omit [DecidableEq V] in
/-- 공통 이웃 변을 지워도 수축은 같다. -/
theorem contractEdge_dropCommon :
    contractEdge (dropCommon G x y) x y = contractEdge G x y := by
  ext p q
  rw [contractEdge_adj, contractEdge_adj]
  constructor
  · rintro ⟨hpq, hp, hq, h | ⟨hpx, h⟩ | ⟨hqx, h⟩⟩
    · exact ⟨hpq, hp, hq, Or.inl (dropCommon_le h)⟩
    · exact ⟨hpq, hp, hq, Or.inr (Or.inl ⟨hpx, dropCommon_le h⟩)⟩
    · exact ⟨hpq, hp, hq, Or.inr (Or.inr ⟨hqx, dropCommon_le h⟩)⟩
  · rintro ⟨hpq, hp, hq, h | ⟨hpx, h⟩ | ⟨hqx, h⟩⟩
    · exact ⟨hpq, hp, hq, Or.inl ((dropCommon_adj_of_ne hp hq).2 h)⟩
    · by_cases hxq : G.Adj x q
      · exact ⟨hpq, hp, hq, Or.inl ((dropCommon_adj_of_ne hp hq).2 (by rw [hpx]; exact hxq))⟩
      · exact ⟨hpq, hp, hq, Or.inr (Or.inl ⟨hpx, dropCommon_adj_y.2 ⟨h, hxq⟩⟩)⟩
    · by_cases hxp : G.Adj x p
      · exact ⟨hpq, hp, hq, Or.inl ((dropCommon_adj_of_ne hp hq).2 (by rw [hqx]; exact hxp.symm))⟩
      · exact ⟨hpq, hp, hq, Or.inr (Or.inr ⟨hqx, dropCommon_adj_y.2 ⟨h, hxp⟩⟩)⟩

/-! ### 비지 않은 단어 -/

/-- 핵심: `G₀ = dropCommon G x y`의 수축 위에서 진술한 구간 조건. -/
theorem isPlanar_of_interval_core [Finite V] (hxy : G.Adj x y)
    (R' : RotationSystem (contractEdge (dropCommon G x y) x y))
    (hR' : R'.eulerChar = 2 * Nat.card (contractEdge (dropCommon G x y) x y).ConnectedComponent)
    (d₀ : (contractEdge (dropCommon G x y) x y).Dart) (hd₀ : d₀.fst = x) (k : ℕ)
    (hk : k ≤ ((contractEdge (dropCommon G x y) x y).neighborSet x).ncard)
    (hA : ∀ j < k, G.Adj x ((R'.rot⁻¹ ^ j) d₀).snd)
    (hX : ∀ j, k ≤ j → j < ((contractEdge (dropCommon G x y) x y).neighborSet x).ncard →
      ¬ G.Adj x ((R'.rot⁻¹ ^ j) d₀).snd)
    (hB : ∀ j, 0 < j → j + 1 < k → ¬ G.Adj y ((R'.rot⁻¹ ^ j) d₀).snd) : IsPlanar G := by
  classical
  have hxy₀ : (dropCommon G x y).Adj x y := (dropCommon_adj_x hxy.ne).2 hxy
  have hKu : ∀ j, (contractEdge (dropCommon G x y) x y).Adj x ((R'.rot⁻¹ ^ j) d₀).snd := by
    intro j
    have h := ((R'.rot⁻¹ ^ j) d₀).adj
    rw [show ((R'.rot⁻¹ ^ j) d₀).toProd.1 = x from (R'.fst_rot_inv_pow d₀ j).trans hd₀] at h
    exact h
  have hA₀ : ∀ j < k, (dropCommon G x y).Adj x ((R'.rot⁻¹ ^ j) d₀).snd :=
    fun j hj ↦ (dropCommon_adj_x hxy.ne).2 (hA j hj)
  have hY₀ : ∀ j, k ≤ j → j < ((contractEdge (dropCommon G x y) x y).neighborSet x).ncard →
      (dropCommon G x y).Adj y ((R'.rot⁻¹ ^ j) d₀).snd := by
    intro j h1 h2
    rcases ((contractEdge_adj_left hxy.ne).1 (hKu j)).2.2 with h | h
    · exact absurd (dropCommon_le h) (hX j h1 h2)
    · exact h
  let D : UncontractData (dropCommon G x y) x y :=
    ⟨hxy₀, dropCommon_no_common hxy.ne, R', d₀, hd₀, k, hk, hA₀, hY₀⟩
  have hR₀ := D.eulerChar_eq hR'
  have hperiod : minimalPeriod ⇑(R'.rot⁻¹) d₀ =
      ((contractEdge (dropCommon G x y) x y).neighborSet x).ncard := by
    rw [RotationSystem.minimalPeriod_rot_inv, hd₀]
  -- 공통 이웃의 자리: `x`쪽 호의 양 끝
  have hloc : ∀ z, G.Adj x z → G.Adj y z →
      0 < k ∧ (z = ((R'.rot⁻¹ ^ (k - 1)) d₀).snd ∨ z = ((R'.rot⁻¹ ^ 0) d₀).snd) := by
    intro z hxz hyz
    have hK : (contractEdge (dropCommon G x y) x y).Adj d₀.fst z := by
      rw [hd₀]
      exact (contractEdge_adj_left hxy.ne).2
        ⟨hxz.ne.symm, hyz.ne.symm, Or.inl ((dropCommon_adj_x hxy.ne).2 hxz)⟩
    obtain ⟨j, hj, hjz⟩ := R'.exists_rot_inv_pow_snd d₀ hK
    rw [hperiod] at hj
    have hjk : j < k := by
      by_contra h
      exact hX j (not_lt.1 h) hj (by rw [hjz]; exact hxz)
    refine ⟨by omega, ?_⟩
    by_cases h0 : j = 0
    · exact Or.inr (by rw [← hjz, h0])
    · by_cases hj1 : j = k - 1
      · exact Or.inl (by rw [← hjz, hj1])
      · exact absurd (by rw [hjz]; exact hyz) (hB j (by omega) (by omega))
  set b₁ := ((R'.rot⁻¹ ^ (k - 1)) d₀).snd with hb₁
  set b₂ := ((R'.rot⁻¹ ^ 0) d₀).snd with hb₂
  have hb₁y : b₁ ≠ y := ((contractEdge_adj_left hxy.ne).1 (hKu (k - 1))).2.1
  have hb₁x : b₁ ≠ x := ((contractEdge_adj_left hxy.ne).1 (hKu (k - 1))).1
  have hb₂y : b₂ ≠ y := ((contractEdge_adj_left hxy.ne).1 (hKu 0)).2.1
  have hb₂x : b₂ ≠ x := ((contractEdge_adj_left hxy.ne).1 (hKu 0)).1
  -- `b₁` 넣기
  obtain ⟨H₁, R₁, hR₁, hG₀H₁, hH₁up, hH₁b₁, hP₁⟩ : ∃ (H₁ : SimpleGraph V) (R₁ : RotationSystem H₁),
      R₁.eulerChar = 2 * Nat.card H₁.ConnectedComponent ∧ dropCommon G x y ≤ H₁ ∧
      H₁ ≤ dropCommon G x y ⊔ edge y b₁ ∧ (0 < k ∧ G.Adj y b₁ → H₁.Adj y b₁) ∧
      (0 < k → ∀ d : H₁.Dart, d.toProd = (x, b₂) → (R₁.rot d).toProd = (x, y)) := by
    by_cases hB₁ : 0 < k ∧ G.Adj y b₁
    · have hk0 := hB₁.1
      have hxb₁ : (dropCommon G x y).Adj x b₁ := hA₀ (k - 1) (by omega)
      let a : (dropCommon G x y).Dart := D.rotationSystem.rot⁻¹ D.yxDart
      let c : (dropCommon G x y).Dart := ⟨(b₁, x), hxb₁.symm⟩
      have hafst : a.fst = y := D.rotationSystem.fst_rot_inv D.yxDart
      have hne : a.fst ≠ c.fst := by rw [hafst]; exact hb₁y.symm
      have hn : ¬ (dropCommon G x y).Adj a.fst c.fst := by
        rw [hafst]
        intro h
        exact (dropCommon_adj_y.1 h).2 (hA (k - 1) (by omega))
      have hface : D.rotationSystem.facePerm.SameCycle a.symm c.symm := by
        refine ⟨((2 : ℕ) : ℤ), ?_⟩
        rw [zpow_natCast, pow_two, Perm.mul_apply, RotationSystem.facePerm_apply,
          RotationSystem.facePerm_apply, Dart.symm_symm]
        have h1 : D.rotationSystem.rot a = D.yxDart := by simp [a]
        rw [h1]
        apply Dart.ext
        rw [show D.yxDart.symm = D.xyDart from rfl, D.rotationSystem_rot_xy hk0]
        rfl
      let E : AddEdgeData (dropCommon G x y) := ⟨D.rotationSystem, a, c, hne, hn, hface⟩
      refine ⟨E.graph, E.rotationSystem, E.eulerChar_eq hR₀, le_sup_left, ?_, ?_, ?_⟩
      · change dropCommon G x y ⊔ edge a.fst c.fst ≤ dropCommon G x y ⊔ edge y b₁
        rw [hafst]
      · intro _
        change (dropCommon G x y ⊔ edge a.fst c.fst).Adj y b₁
        rw [hafst]
        exact Or.inr ((edge_adj _ _ _ _).2 ⟨Or.inl ⟨rfl, rfl⟩, hb₁y.symm⟩)
      · intro _ d hd
        let e : (dropCommon G x y).Dart := ⟨(x, b₂), hA₀ 0 hk0⟩
        have hea : e ≠ a := fun h ↦ hxy.ne ((congrArg (·.fst) h).trans hafst)
        have hec : e ≠ c := fun h ↦ hb₁x (congrArg (·.fst) h).symm
        rw [E.rotationSystem_rot_toProd_of_ne d e hd hea hec]
        rw [D.rotationSystem_rot_to_xy hk0 e rfl]
        rfl
    · refine ⟨dropCommon G x y, D.rotationSystem, hR₀, le_rfl, le_sup_left,
        fun h ↦ absurd h hB₁, ?_⟩
      intro hk0 d hd
      rw [D.rotationSystem_rot_to_xy hk0 d hd]
      rfl
  -- `b₂` 넣기
  obtain ⟨H₂, hH₂, hH₁H₂, hH₂b₂⟩ : ∃ H₂ : SimpleGraph V, IsPlanar H₂ ∧ H₁ ≤ H₂ ∧
      (2 ≤ k ∧ G.Adj y b₂ → H₂.Adj y b₂) := by
    by_cases hB₂ : 2 ≤ k ∧ G.Adj y b₂
    · have hk0 : 0 < k := by omega
      have hb₁₂ : b₁ ≠ b₂ := by
        intro h
        have := R'.eq_of_rot_inv_pow_snd_eq d₀ (by rw [hperiod]; omega) (by rw [hperiod]; omega) h
        omega
      have hyx₁ : H₁.Adj y x := hG₀H₁ hxy₀.symm
      have hb₂x₁ : H₁.Adj b₂ x := hG₀H₁ (hA₀ 0 hk0).symm
      let a : H₁.Dart := ⟨(y, x), hyx₁⟩
      let c : H₁.Dart := R₁.rot⁻¹ ⟨(b₂, x), hb₂x₁⟩
      have hcfst : c.fst = b₂ := R₁.fst_rot_inv _
      have hne : a.fst ≠ c.fst := by rw [hcfst]; exact hb₂y.symm
      have hn : ¬ H₁.Adj a.fst c.fst := by
        rw [hcfst]
        intro h
        rcases hH₁up h with h | h
        · exact (dropCommon_adj_y.1 h).2 (hA 0 hk0)
        · rcases ((edge_adj _ _ _ _).1 h).1 with ⟨-, h'⟩ | ⟨h', -⟩
          · exact hb₁₂ h'.symm
          · exact hb₁y h'.symm
      have hface : R₁.facePerm.SameCycle a.symm c.symm := by
        refine SameCycle.symm ⟨((2 : ℕ) : ℤ), ?_⟩
        rw [zpow_natCast, pow_two, Perm.mul_apply, RotationSystem.facePerm_apply,
          RotationSystem.facePerm_apply, Dart.symm_symm]
        have h1 : R₁.rot c = ⟨(b₂, x), hb₂x₁⟩ := by simp [c]
        rw [h1]
        apply Dart.ext
        exact hP₁ hk0 _ rfl
      let E : AddEdgeData H₁ := ⟨R₁, a, c, hne, hn, hface⟩
      refine ⟨E.graph, ⟨E.rotationSystem, E.eulerChar_eq hR₁⟩, le_sup_left, ?_⟩
      intro _
      change (H₁ ⊔ edge y c.fst).Adj y b₂
      rw [hcfst]
      exact Or.inr ((edge_adj _ _ _ _).2 ⟨Or.inl ⟨rfl, rfl⟩, hb₂y.symm⟩)
    · exact ⟨H₁, ⟨R₁, hR₁⟩, le_rfl, fun h ↦ absurd h hB₂⟩
  -- 원래 그래프는 `H₂`에 들어간다
  apply hH₂.mono
  intro p q h
  by_cases h₀ : (dropCommon G x y).Adj p q
  · exact hH₁H₂ (hG₀H₁ h₀)
  have hcond : (p = y ∧ G.Adj x q ∧ G.Adj y q) ∨ (q = y ∧ G.Adj x p ∧ G.Adj y p) := by
    by_contra hc
    exact h₀ (dropCommon_adj.2 ⟨h, hc⟩)
  -- `y`와 공통 이웃을 잇는 변은 `H₂`에 있다
  have hyz : ∀ z, G.Adj x z → G.Adj y z → H₂.Adj y z := by
    intro z hxz hyz'
    obtain ⟨hk0, hz | hz⟩ := hloc z hxz hyz'
    · rw [hz] at hyz' ⊢
      exact hH₁H₂ (hH₁b₁ ⟨hk0, hyz'⟩)
    · by_cases hk2 : 2 ≤ k
      · rw [hz] at hyz' ⊢
        exact hH₂b₂ ⟨hk2, hyz'⟩
      · have hk1 : k - 1 = 0 := by omega
        have hb : b₂ = b₁ := by rw [hb₁, hb₂, hk1]
        rw [hz, hb] at hyz' ⊢
        exact hH₁H₂ (hH₁b₁ ⟨hk0, hyz'⟩)
  rcases hcond with ⟨hp, hxq, hyq⟩ | ⟨hq, hxp, hyp⟩
  · rw [hp]
    exact hyz q hxq hyq
  · rw [hq]
    exact (hyz p hxp hyp).symm

/-- 수축 그래프를 일반화한 형태: `G₀/xy = K`로 옮긴다. -/
theorem isPlanar_of_interval_gen [Finite V] (hxy : G.Adj x y) (K : SimpleGraph V)
    (hK : contractEdge (dropCommon G x y) x y = K) (R' : RotationSystem K)
    (hR' : R'.eulerChar = 2 * Nat.card K.ConnectedComponent)
    (d₀ : K.Dart) (hd₀ : d₀.fst = x) (k : ℕ) (hk : k ≤ (K.neighborSet x).ncard)
    (hA : ∀ j < k, G.Adj x ((R'.rot⁻¹ ^ j) d₀).snd)
    (hX : ∀ j, k ≤ j → j < (K.neighborSet x).ncard → ¬ G.Adj x ((R'.rot⁻¹ ^ j) d₀).snd)
    (hB : ∀ j, 0 < j → j + 1 < k → ¬ G.Adj y ((R'.rot⁻¹ ^ j) d₀).snd) : IsPlanar G := by
  subst hK
  exact isPlanar_of_interval_core hxy R' hR' d₀ hd₀ k hk hA hX hB

omit [DecidableEq V] in
/-- 블루프린트 `lem:S`: 구간 조건이면 꼭짓점을 나눠도 평면이다. 유한성 이외의 결정 가능성 인스턴스는
요구하지 않는다. -/
theorem IsPlanar.of_contractEdge_of_interval [Finite V] (hxy : G.Adj x y)
    (R' : RotationSystem (contractEdge G x y))
    (hR' : R'.eulerChar = 2 * Nat.card (contractEdge G x y).ConnectedComponent)
    (hw : IntervalWord G x y R') : IsPlanar G := by
  classical
  rcases hw with h0 | ⟨d₀, hd₀, k, hk, hA, hX, hB⟩
  · exact isPlanar_of_contractEdge_of_isolated hxy ⟨R', hR'⟩ h0
  · exact isPlanar_of_interval_gen hxy _ contractEdge_dropCommon R' hR' d₀ hd₀ k hk
      hA hX hB

end Kuratowski
