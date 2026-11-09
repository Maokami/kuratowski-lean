import Kuratowski.AlternatingNeighbors
import Kuratowski.CommonNeighbors
import Kuratowski.Contractible
import Kuratowski.NeighborWord
import Kuratowski.Reduction
import Kuratowski.Subdivision

/-!
# 쿠라토프스키 정리 (블루프린트 `thm:hard`, `thm:kuratowski`)

변 수에 대한 강한 귀납으로 KF 유한 그래프가 평면임을 증명한다 (`isPlanar_of_kuratowskiFree`).
`isPlanar_or_threeConnected`로 `G`가 평면이거나 3-연결이다. 지지 집합이 4개 이하이면 작은 그래프다.
그렇지 않으면 수축해도 3-연결인 변 `xy`를 고르고, 귀납 가정으로 `G/xy`의 종수 0 회전 `R'`을 얻는다.
`R'`의 `x` 둘레 역순 이웃 열에서 원래 `x`, `y` 인접을 읽은 단어(`RotationSystem.neighborWord`)를
분류한다. `X/B`, `Y/B` 위치는 원래 `G`에서 `x`, `y`의 이웃이 각각 셋 이상이므로 각각 둘 이상이다.
- 구간에 모이면 꼭짓점 나누기(`IsPlanar.of_contractEdge_of_interval`)로 `G`가 평면이다.
- `B`가 셋 이상이거나 교대이면 J2의 사이클 `C`와 위치 `p`로 `K₅` 또는 `K₃,₃`의 세분을 만들어 KF에
  모순이다.
마지막으로 쉬운 방향 `IsPlanar.not_containsSubdivision`과 합쳐 `isPlanar_iff_kuratowskiFree`를 얻는다.

보조 사실:
- `CyclicSequence.mono`: 부분 그래프의 순환 꼭짓점 수열을 큰 그래프로 옮긴다.
- `exists_two_mem_ne_of_three_le`: 원소가 셋 이상인 집합에서 한 점을 피하는 서로 다른 두 원소.
- `RotationSystem.exists_zmod_rot_inv_pow_snd`, `RotationSystem.eq_of_zmod_rot_inv_pow_snd_eq`:
  `v`의 이웃 수가 `N`일 때 `i : ZMod N ↦ (ρ⁻¹^i.val d₀).snd`는 `v`의 이웃 위로의 전단사다.
- `RotationSystem.two_le_card_of_two_adj`: 성질 `P`를 가진 서로 다른 이웃이 둘이면 `P` 위치도 둘 이상이다.
-/

namespace Kuratowski

open SimpleGraph Equiv Equiv.Perm Function

variable {V : Type*}

namespace CyclicSequence

variable {G H : SimpleGraph V} {m : ℕ}

/-- 부분 그래프의 순환 꼭짓점 수열은 큰 그래프의 순환 꼭짓점 수열이다. -/
def mono (C : CyclicSequence H m) (hle : H ≤ G) : CyclicSequence G m where
  length_ge_three := C.length_ge_three
  vertex := C.vertex
  adj_next i := hle (C.adj_next i)

@[simp] theorem mono_apply (C : CyclicSequence H m) (hle : H ≤ G) (i : ZMod m) :
    C.mono hle i = C i := rfl

end CyclicSequence

/-- 원소가 셋 이상인 집합에는 주어진 점과 다른 서로 다른 두 원소가 있다. -/
theorem exists_two_mem_ne_of_three_le [Finite V] {s : Set V} (hs : 3 ≤ s.ncard) (y : V) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ a ≠ y ∧ b ≠ y := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff (s := s)).1 (by omega)
  by_cases hay : a = y
  · subst hay
    exact ⟨b, hb, c, hc, hbc, fun h ↦ hab h.symm, fun h ↦ hac h.symm⟩
  · by_cases hby : b = y
    · subst hby
      exact ⟨a, ha, c, hc, hac, hay, fun h ↦ hbc h.symm⟩
    · exact ⟨a, ha, b, hb, hab, hay, hby⟩

namespace RotationSystem

variable [Finite V] {H : SimpleGraph V} (R : RotationSystem H)

/-- `v`의 이웃은 모두 어떤 `i : ZMod N`에 대해 `ρ⁻¹^i.val d₀`의 끝점이다 (`N`은 `v`의 이웃 수). -/
theorem exists_zmod_rot_inv_pow_snd (d₀ : H.Dart) {v : V} (hd₀ : d₀.fst = v)
    [NeZero (H.neighborSet v).ncard] {z : V} (hz : H.Adj v z) :
    ∃ i : ZMod (H.neighborSet v).ncard, ((R.rot⁻¹ ^ i.val) d₀).snd = z := by
  subst hd₀
  obtain ⟨j, hj, hjz⟩ := R.exists_rot_inv_pow_snd d₀ hz
  rw [R.minimalPeriod_rot_inv] at hj
  refine ⟨(j : ZMod _), ?_⟩
  rw [ZMod.val_natCast_of_lt hj]
  exact hjz

/-- `i ↦ (ρ⁻¹^i.val d₀).snd`는 `ZMod N` 위에서 단사다. -/
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

/-- 성질 `P`를 가진 `v`의 서로 다른 이웃이 둘이면, 끝점이 `P`인 위치의 집합 `S`의 크기는 2 이상이다. -/
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

section Main

variable {G : SimpleGraph V} {x y : V}

/-- 블루프린트 `thm:hard`의 마지막 단계. KF인 3-연결 `G`의 변 `xy`를 수축해도 3-연결이고 `G/xy`에
종수 0 회전 `R'`이 있으면 `G`는 평면이다. -/
theorem isPlanar_of_contractible [Finite V] (hKF : KuratowskiFree G) (h3 : ThreeConnected G)
    (hxy : G.Adj x y) (h3' : ThreeConnected (contractEdge G x y))
    (R' : RotationSystem (contractEdge G x y))
    (hR' : R'.eulerChar = 2 * Nat.card (contractEdge G x y).ConnectedComponent) :
    IsPlanar G := by
  classical
  -- 원래 `G`에서 `x`, `y`의 이웃은 각각 셋 이상이므로 서로를 뺀 이웃이 각각 둘 이상이다.
  have hdx := ConnectedOn.ncard_neighborSet_ge h3 (x := x) (G.mem_support.2 ⟨y, hxy⟩)
  have hdy := ConnectedOn.ncard_neighborSet_ge h3 (x := y) (G.mem_support.2 ⟨x, hxy.symm⟩)
  obtain ⟨a₁, ha₁, a₂, ha₂, ha₁₂, ha₁y, ha₂y⟩ := exists_two_mem_ne_of_three_le hdx y
  obtain ⟨b₁, hb₁, b₂, hb₂, hb₁₂, hb₁x, hb₂x⟩ := exists_two_mem_ne_of_three_le hdy x
  have hx' : ∀ z, G.Adj x z → z ≠ y → (contractEdge G x y).Adj x z := fun z hz hzy ↦
    ⟨hz.ne, hxy.ne, hzy, Or.inl hz⟩
  have hy' : ∀ z, G.Adj y z → z ≠ x → (contractEdge G x y).Adj x z := fun z hz hzx ↦
    ⟨fun h ↦ hzx h.symm, hxy.ne, hz.ne', Or.inr (Or.inl ⟨rfl, hz⟩)⟩
  -- `G/xy`에서 `x`의 이웃 수 `N`은 셋 이상이다.
  have hN := ConnectedOn.ncard_neighborSet_ge h3' (x := x)
    ((contractEdge G x y).mem_support.2 ⟨a₁, hx' a₁ ha₁ ha₁y⟩)
  have : NeZero ((contractEdge G x y).neighborSet x).ncard := ⟨by omega⟩
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : (contractEdge G x y).Dart, d₀.fst = x :=
    ⟨⟨(x, a₁), hx' a₁ ha₁ ha₁y⟩, rfl⟩
  -- J2: `G/xy - x = G - {x, y}`의 사이클 `C`가 이웃 `u_j`를 위치 `p j`에서 지난다.
  obtain ⟨-, m, C, -, -, p, -, hinc, hpm, hCp⟩ :=
    R'.exists_cyclicSequence_delVertex_neighbors hR' x (by omega)
      (ConnectedOn.deleteVertex (k := 2) h3' x) d₀ hd₀
  have : NeZero m := C.neZero
  have hle : deleteVertices (contractEdge G x y) {x} ≤ G := by
    rw [deleteVertices_contractEdge_left]
    exact deleteVertices_le _ _
  have hxC : x ∉ Set.range (C.mono hle) := by
    rintro ⟨i, hi⟩
    exact ((deleteVertices_adj _ _ _ _).1 (C.adj_next i)).2.1 (Set.mem_singleton_iff.2 hi)
  have hyC : y ∉ Set.range (C.mono hle) := by
    rintro ⟨i, hi⟩
    exact (contractEdge_adj.1 ((deleteVertices_adj _ _ _ _).1 (C.adj_next i)).1).2.1 hi
  have hpos : ∀ t : ZMod ((contractEdge G x y).neighborSet x).ncard,
      C.mono hle (p t.val : ZMod m) = ((R'.rot⁻¹ ^ t.val) d₀).snd :=
    fun t ↦ hCp t.val (ZMod.val_lt t)
  have hXC : ∀ t ∈ CyclicWord.xPositions (R'.neighborWord d₀),
      G.Adj x (C.mono hle (p t.val : ZMod m)) := by
    intro t ht
    rw [hpos t]
    exact (R'.mem_xPositions_neighborWord d₀).1 ht
  have hYC : ∀ t ∈ CyclicWord.yPositions (R'.neighborWord d₀),
      G.Adj y (C.mono hle (p t.val : ZMod m)) := by
    intro t ht
    rw [hpos t]
    exact (R'.mem_yPositions_neighborWord d₀).1 ht
  -- 단어의 `X/B`, `Y/B` 위치는 각각 둘 이상이다.
  have hX : 2 ≤ (CyclicWord.xPositions (R'.neighborWord d₀)).card :=
    R'.two_le_card_of_two_adj d₀ hd₀ _ (G.Adj x) (fun _ ↦ R'.mem_xPositions_neighborWord d₀)
      ha₁₂ (hx' a₁ ha₁ ha₁y) (hx' a₂ ha₂ ha₂y) ha₁ ha₂
  have hY : 2 ≤ (CyclicWord.yPositions (R'.neighborWord d₀)).card :=
    R'.two_le_card_of_two_adj d₀ hd₀ _ (G.Adj y) (fun _ ↦ R'.mem_yPositions_neighborWord d₀)
      hb₁₂ (hy' b₁ hb₁ hb₁x) (hy' b₂ hb₂ hb₂x) hb₁ hb₂
  rcases CyclicWord.classify (R'.neighborWord d₀) hX hY with hc | hB | halt
  · -- (a) 구간에 모임: 꼭짓점 나누기
    exact IsPlanar.of_contractEdge_of_interval hxy R' hR'
      (R'.intervalWord_of_clustered d₀ hd₀ hc)
  · -- (b) `B`가 셋 이상: `K₅`의 세분
    exfalso
    apply hKF.1
    obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.1 hB
    have hboth : ∀ t ∈ CyclicWord.bothPositions (R'.neighborWord d₀),
        G.Adj x (C.mono hle (p t.val : ZMod m)) ∧ G.Adj y (C.mono hle (p t.val : ZMod m)) := by
      intro t ht
      rw [← CyclicWord.inter_positions, Finset.mem_inter] at ht
      exact ⟨hXC t ht.1, hYC t ht.2⟩
    have hne : ∀ s t : ZMod ((contractEdge G x y).neighborSet x).ncard, s ≠ t →
        (p s.val : ZMod m) ≠ (p t.val : ZMod m) := by
      intro s t hst h
      apply hst
      apply R'.eq_of_zmod_rot_inv_pow_snd_eq d₀ hd₀
      rw [← hpos s, ← hpos t, h]
    exact containsSubdivision_K5_of_three_common (C.mono hle) hxy hxC hyC (hne _ _ hij)
      (hne _ _ hik) (hne _ _ hjk) (hboth i hi) (hboth j hj) (hboth k hk)
  · -- (c) 교대: `K₃,₃`의 세분
    exfalso
    apply hKF.2
    obtain ⟨u, hu, w, hw, ⟨a, ha, hua⟩, b, hb, hwb⟩ := halt
    exact containsSubdivision_K33_of_alternating (C.mono hle) hxy hxC hyC
      (CyclicWord.sbtw_cast_positions p hpm hinc hua)
      (CyclicWord.sbtw_cast_positions p hpm hinc hwb)
      (hYC u hu) (hYC w hw) (hXC a ha) (hXC b hb)

/-- 귀납 단계: KF인 `G`에서 변이 더 적은 KF 그래프가 모두 평면이면 `G`도 평면이다. -/
theorem isPlanar_of_kuratowskiFree_of_lt [Finite V] (hKF : KuratowskiFree G)
    (hIH : ∀ H : SimpleGraph V, KuratowskiFree H → H.edgeSet.ncard < G.edgeSet.ncard →
      IsPlanar H) :
    IsPlanar G := by
  rcases isPlanar_or_threeConnected hKF hIH with hP | h3
  · exact hP
  by_cases hs : G.support.ncard ≤ 4
  · exact isPlanar_of_ncard_support_le_four G hs
  obtain ⟨x, y, hxy, h3'⟩ := h3.exists_contractible (by omega)
  obtain ⟨R', hR'⟩ := hIH _ (hKF.contractEdge hxy) (ncard_edgeSet_contractEdge_lt hxy)
  exact isPlanar_of_contractible hKF h3 hxy h3' R' hR'

/-- 블루프린트 `thm:hard` (쿠라토프스키 정리, 어려운 방향): `K₅`의 세분도 `K₃,₃`의 세분도
갖지 않는 유한 그래프는 평면 그래프다. -/
theorem isPlanar_of_kuratowskiFree [Finite V] (h5 : ¬ ContainsSubdivision G K5)
    (h33 : ¬ ContainsSubdivision G K33) : IsPlanar G := by
  suffices key : ∀ n (H : SimpleGraph V), H.edgeSet.ncard = n → KuratowskiFree H → IsPlanar H from
    key _ G rfl ⟨h5, h33⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hn hKF
    exact isPlanar_of_kuratowskiFree_of_lt hKF fun K hK hlt ↦ ih _ (by omega) K rfl hK

/-- 블루프린트 `thm:kuratowski` (쿠라토프스키 정리): 유한 그래프가 평면 그래프일 필요충분조건은
`K₅`의 세분도 `K₃,₃`의 세분도 갖지 않는 것이다. -/
theorem isPlanar_iff_kuratowskiFree [Finite V] :
    IsPlanar G ↔ ¬ ContainsSubdivision G K5 ∧ ¬ ContainsSubdivision G K33 := by
  classical
  exact ⟨IsPlanar.not_containsSubdivision, fun h ↦ isPlanar_of_kuratowskiFree h.1 h.2⟩

end Main

end Kuratowski
