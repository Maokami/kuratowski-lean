import Kuratowski.ConnectedContraction

/-!
# 수축 가능한 변 (블루프린트 `thm:contractible`)

지지 집합이 5개 이상인 3-연결 그래프에는 수축해도 3-연결인 변이 있다
(`ThreeConnected.exists_contractible`). Diestel, *Graph Theory* 6판 보조정리 3.2.4(5판 3.2.1)의
증명을 따른다. 지지 집합 조건은 `G ≠ K₄`를 대신하며, 수축의 지지 집합이 4개 이상이라는 데만 쓰인다.

수축 가능한 변이 없다고 하자. 변 `xy`마다 `{x, y, z}`가 `G`를 분리하는 `z`가 있다. 그런 `(x, y, z)`와
`G - {x, y, z}`의 성분 `C`를 `|C|`가 가장 작도록 고른다. `z`는 `C`에 이웃 `v`가 있고, 변 `zv`에도
분리 집합 `{z, v, w}`가 있다. `x ∼ y`이므로 `G - {z, v, w}`에는 `x`, `y`를 피하는 성분 `D`가 있다.
`v`의 `D` 안 이웃은 `C`에 있으므로 `D ⊆ C`이고, `v ∈ C \ D`이므로 `|D| < |C|`라 모순이다.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Finite V]

/-- 블루프린트 `thm:contractible` (Diestel 6판 보조정리 3.2.4): 지지 집합이 5개 이상인 3-연결 그래프에는
수축해도 3-연결인 변이 있다. -/
theorem ThreeConnected.exists_contractible (hG : ThreeConnected G) (h5 : 5 ≤ G.support.ncard) :
    ∃ x y, G.Adj x y ∧ ThreeConnected (contractEdge G x y) := by
  classical
  by_contra hno
  simp only [not_exists, not_and] at hno
  -- 분리 집합 `{x, y, z}`와 성분의 대표 `c`
  let Adm : V → V → V → V → Prop := fun x y z c ↦ G.Adj x y ∧ z ∈ G.support ∧ z ≠ x ∧
    z ≠ y ∧ Separates G {x, y, z} ∧ c ∈ G.support \ {x, y, z}
  have hex : ∃ n, ∃ x y z c, Adm x y z c ∧ (sepComponent G {x, y, z} c).ncard = n := by
    have hne : G.support.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hxy⟩ := hx
    obtain ⟨z, hz, hzx, hzy, hsep⟩ :=
      exists_separates_of_not_threeConnected hG h5 hxy (hno x y hxy)
    obtain ⟨u, hu, -⟩ := id hsep
    exact ⟨_, x, y, z, u, ⟨hxy, hz, hzx, hzy, hsep, hu⟩, rfl⟩
  obtain ⟨x, y, z, c, ⟨hxy, hz, hzx, hzy, hsep, hc⟩, hn⟩ := Nat.find_spec hex
  have hmin : ∀ x' y' z' c', Adm x' y' z' c' →
      Nat.find hex ≤ (sepComponent G {x', y', z'} c').ncard :=
    fun x' y' z' c' h ↦ Nat.find_min' hex ⟨x', y', z', c', h, rfl⟩
  set T : Set V := {x, y, z} with hTdef
  set C := sepComponent G T c with hCdef
  have hT3 : T.ncard = 3 :=
    Set.ncard_eq_three.2 ⟨x, y, z, hxy.ne, fun e ↦ hzx e.symm, fun e ↦ hzy e.symm, rfl⟩
  -- `z`의 `C` 안 이웃 `v`와 변 `zv`의 분리 집합 `{z, v, w}`
  obtain ⟨v, hvC, hzv⟩ := exists_adj_mem_sepComponent hG hT3 hsep hc (t := z) (by simp [T])
  have hvT : v ≠ x ∧ v ≠ y ∧ v ≠ z := by
    have := hvC.1.2
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at this
    exact this
  obtain ⟨w, hw, hwz, hwv, hsep'⟩ :=
    exists_separates_of_not_threeConnected hG h5 hzv (hno z v hzv)
  set T' : Set V := {z, v, w} with hT'def
  have hT'3 : T'.ncard = 3 :=
    Set.ncard_eq_three.2 ⟨z, v, w, hzv.ne, fun e ↦ hwz e.symm, fun e ↦ hwv e.symm, rfl⟩
  have hmem' : ∀ s, s ∈ T' ↔ s = z ∨ s = v ∨ s = w := by
    intro s
    simp [T']
  -- `x`, `y` 가운데 `T'`에 없는 쪽은 서로 이어져 있다
  have hr : ∃ r ∈ G.support \ T', ∀ s, (s = x ∨ s = y) → s ∉ T' →
      (deleteVertices G T').Reachable r s := by
    by_cases hxT' : x ∈ T'
    · have hxw : x = w := by
        rcases (hmem' x).1 hxT' with h | h | h
        · exact absurd h.symm hzx
        · exact absurd h.symm hvT.1
        · exact h
      have hyT' : y ∉ T' := by
        intro h
        rcases (hmem' y).1 h with h | h | h
        · exact hzy h.symm
        · exact hvT.2.1 h.symm
        · exact hxy.ne (hxw.trans h.symm)
      refine ⟨y, ⟨hxy.mem_support_right, hyT'⟩, ?_⟩
      rintro s (rfl | rfl) hs
      · exact absurd hxT' hs
      · exact .refl _
    · refine ⟨x, ⟨hxy.mem_support_left, hxT'⟩, ?_⟩
      rintro s (rfl | rfl) hs
      · exact .refl _
      · exact Adj.reachable ⟨hxy, hxT', hs⟩
  obtain ⟨r, hr, hrs⟩ := hr
  -- `r`에서 닿지 않는 성분 `D`는 `x`, `y`를 피한다
  obtain ⟨d₀, hd₀, hrd₀⟩ : ∃ d₀ ∈ G.support \ T', ¬ (deleteVertices G T').Reachable r d₀ := by
    obtain ⟨u', hu', v', hv', huv'⟩ := hsep'
    by_cases h : (deleteVertices G T').Reachable r u'
    · exact ⟨v', hv', fun h' ↦ huv' (h.symm.trans h')⟩
    · exact ⟨u', hu', h⟩
  set D := sepComponent G T' d₀ with hDdef
  have hxyD : ∀ s, (s = x ∨ s = y) → s ∉ D := by
    intro s hs hsD
    exact hrd₀ ((hrs s hs hsD.1.2).trans hsD.2.symm)
  have hnotT : ∀ a ∈ D, a ∉ T := by
    intro a ha haT
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at haT
    rcases haT with rfl | rfl | rfl
    · exact hxyD _ (Or.inl rfl) ha
    · exact hxyD _ (Or.inr rfl) ha
    · exact ha.1.2 ((hmem' _).2 (Or.inl rfl))
  -- `D`의 걸음은 `D` 안에 머물고 `T`를 피한다
  have stay : ∀ {a b : V} (p : (deleteVertices G T').Walk a b), a ∈ D →
      (deleteVertices G T).Reachable a b ∧ b ∈ D := by
    intro a b p
    induction p with
    | nil => exact fun h ↦ ⟨.refl _, h⟩
    | @cons a a' b h p ih =>
      intro ha
      have ha' : a' ∈ D := ⟨⟨h.1.mem_support_right, h.2.2⟩, ha.2.trans h.reachable⟩
      obtain ⟨h1, h2⟩ := ih ha'
      have hT : (deleteVertices G T).Adj a a' := ⟨h.1, hnotT a ha, hnotT a' ha'⟩
      exact ⟨hT.reachable.trans h1, h2⟩
  -- `v`의 `D` 안 이웃 `d`는 `C`에 있다
  obtain ⟨d, hdD, hvd⟩ :=
    exists_adj_mem_sepComponent hG hT'3 hsep' hd₀ (t := v) ((hmem' v).2 (Or.inr (Or.inl rfl)))
  have hdC : d ∈ C := ⟨⟨hdD.1.1, hnotT d hdD⟩, hvC.2.trans (Adj.reachable ⟨hvd, hvC.1.2,
    hnotT d hdD⟩)⟩
  have hDC : D ⊆ C := by
    intro a ha
    obtain ⟨p⟩ := (hdD.2.symm.trans ha.2 : (deleteVertices G T').Reachable d a)
    obtain ⟨hda, -⟩ := stay p hdD
    exact ⟨⟨ha.1.1, hnotT a ha⟩, hdC.2.trans hda⟩
  -- `v ∈ C \ D`이므로 `D`가 더 작아 최소성에 모순
  have hvD : v ∉ D := fun h ↦ h.1.2 ((hmem' v).2 (Or.inr (Or.inl rfl)))
  have hlt : D.ncard < C.ncard := Set.ncard_lt_ncard ⟨hDC, fun h ↦ hvD (h hvC)⟩
  have hle : Nat.find hex ≤ D.ncard := hmin z v w d₀ ⟨hzv, hw, hwz, hwv, hsep', hd₀⟩
  omega

end Kuratowski
