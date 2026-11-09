import Kuratowski.Connected
import Kuratowski.Contract

/-!
# 3-연결 그래프의 수축과 분리 집합

Diestel, *Graph Theory* 6판 보조정리 3.2.4(5판 3.2.1)의 증명에 쓰는 사실들.

* `Separates G T`: `T`를 지우면 지지 집합의 두 점이 끊어진다. `sepComponent G T c`는 `G - T`에서 `c`의
  성분(지지 집합 안)이다.
* `support_contractEdge_of_threeConnected`: 3-연결이고 지지 집합이 5개 이상이면 수축의 지지 집합은
  `G.support \ {y}`다.
* `exists_separates_of_not_threeConnected`: 수축이 3-연결이 아니면 `{x, y, z}`가 `G`를 분리하는 `z`가
  있다 (Diestel의 첫 문단).
* `exists_adj_mem_sepComponent`: 크기 3인 분리 집합의 각 점은 `G - T`의 모든 성분에 이웃이 있다.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- `T`를 지우면 지지 집합의 두 점이 끊어진다. -/
def Separates (G : SimpleGraph V) (T : Set V) : Prop :=
  ∃ u ∈ G.support \ T, ∃ v ∈ G.support \ T, ¬ (deleteVertices G T).Reachable u v

/-- `G - T`에서 `c`가 속한 성분. 지지 집합 안에서만 센다. -/
def sepComponent (G : SimpleGraph V) (T : Set V) (c : V) : Set V :=
  {w | w ∈ G.support \ T ∧ (deleteVertices G T).Reachable c w}

/-- 지지 집합 밖의 점은 지워도 지우지 않아도 같다. -/
theorem deleteVertices_inter_support (T : Set V) :
    deleteVertices G (T ∩ G.support) = deleteVertices G T := by
  ext a b
  simp only [deleteVertices_adj, Set.mem_inter_iff, not_and]
  constructor
  · rintro ⟨h, ha, hb⟩
    exact ⟨h, fun h' ↦ ha h' h.mem_support_left, fun h' ↦ hb h' h.mem_support_right⟩
  · rintro ⟨h, ha, hb⟩
    exact ⟨h, fun h' _ ↦ ha h', fun h' _ ↦ hb h'⟩

/-- 변마다 도달 가능성을 옮기는 사상은 도달 가능성을 옮긴다. -/
theorem reachable_of_adj_reachable {H H' : SimpleGraph V} (φ : V → V)
    (hφ : ∀ a b, H.Adj a b → H'.Reachable (φ a) (φ b)) {u v : V} (h : H.Reachable u v) :
    H'.Reachable (φ u) (φ v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .refl _
  | cons hab _ ih => exact (hφ _ _ hab).trans ih

variable {x y : V}

/-- `x`를 지우지 않으면 `G`의 걸음은 `y`를 `x`로 보내 수축 그래프의 걸음이 된다. -/
theorem reachable_contractEdge_of_not_mem (hxy : x ≠ y) {S : Set V} (hxS : x ∉ S) {u v : V}
    (hu : u ≠ y) (hv : v ≠ y) (h : (deleteVertices G (S \ {y})).Reachable u v) :
    (deleteVertices (contractEdge G x y) S).Reachable u v := by
  classical
  let φ : V → V := fun w ↦ if w = y then x else w
  have key : ∀ a b, (deleteVertices G (S \ {y})).Adj a b →
      (deleteVertices (contractEdge G x y) S).Reachable (φ a) (φ b) := by
    rintro a b ⟨hab, ha, hb⟩
    have ha' : a ≠ y → a ∉ S := fun h' h'' ↦ ha ⟨h'', h'⟩
    have hb' : b ≠ y → b ∉ S := fun h' h'' ↦ hb ⟨h'', h'⟩
    by_cases hay : a = y
    · subst hay
      have hby : b ≠ a := hab.ne.symm
      simp only [φ, ↓reduceIte, hby]
      by_cases hbx : b = x
      · rw [hbx]
      · exact Adj.reachable ⟨⟨fun e ↦ hbx e.symm, hxy, hby, Or.inr (Or.inl ⟨rfl, hab⟩)⟩, hxS,
          hb' hby⟩
    · by_cases hby : b = y
      · subst hby
        simp only [φ, hay, ↓reduceIte]
        by_cases hax : a = x
        · rw [hax]
        · exact Adj.reachable ⟨⟨hax, hay, hxy, Or.inr (Or.inr ⟨rfl, hab.symm⟩)⟩, ha' hay, hxS⟩
      · simp only [φ, hay, hby, ↓reduceIte]
        exact Adj.reachable ⟨⟨hab.ne, hay, hby, Or.inl hab⟩, ha' hay, hb' hby⟩
  have := reachable_of_adj_reachable φ key h
  simpa [φ, hu, hv] using this

/-- `G`에서 `S`와 `y`를 피하는 걸음은 수축 그래프에서 `S`를 피하는 걸음이다. -/
theorem reachable_contractEdge_of_union (S : Set V) {u v : V}
    (h : (deleteVertices G (S ∪ {y})).Reachable u v) :
    (deleteVertices (contractEdge G x y) S).Reachable u v := by
  refine h.mono fun a b hab ↦ ?_
  obtain ⟨hab, ha, hb⟩ := hab
  simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at ha hb
  exact ⟨⟨hab.ne, ha.2, hb.2, Or.inl hab⟩, ha.1, hb.1⟩

variable [Finite V]

/-- 3-연결 그래프에서 `y`가 아닌 지지점은 `y`가 아닌 이웃이 있다. -/
theorem exists_adj_ne_of_threeConnected (hG : ThreeConnected G) (h5 : 5 ≤ G.support.ncard)
    {w : V} (hw : w ∈ G.support) (hwy : w ≠ y) : ∃ w', w' ≠ y ∧ G.Adj w w' := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  -- `y`를 지우면 `w`가 고립된다. 다른 생존점이 있다.
  have hbig : 2 ≤ (G.support \ {y}).ncard := by
    have h2 := Set.ncard_le_ncard_sdiff_add_ncard G.support {y}
    rw [Set.ncard_singleton] at h2
    omega
  obtain ⟨w', hw', hne⟩ := Set.exists_ne_of_one_lt_ncard hbig w
  refine not_connectedOn_of_isolated G 3 G.support {y} (by simp) ⟨hw, hwy⟩ hw' hne.symm ?_ hG
  rintro t ⟨ht, -, hty⟩
  exact hno t hty ht

/-- 3-연결이고 지지 집합이 5개 이상이면 수축의 지지 집합은 `G.support \ {y}`다. -/
theorem support_contractEdge_of_threeConnected (hG : ThreeConnected G) (h5 : 5 ≤ G.support.ncard)
    (hxy : G.Adj x y) : (contractEdge G x y).support = G.support \ {y} := by
  ext w
  constructor
  · rintro ⟨w', hpq, hwy, -, h | ⟨rfl, -⟩ | ⟨-, h⟩⟩
    · exact ⟨h.mem_support_left, hwy⟩
    · exact ⟨hxy.mem_support_left, hwy⟩
    · exact ⟨h.mem_support_right, hwy⟩
  · rintro ⟨hw, hwy⟩
    obtain ⟨w', hw'y, hww'⟩ := exists_adj_ne_of_threeConnected hG h5 hw hwy
    exact ⟨w', hww'.ne, hwy, hw'y, Or.inl hww'⟩

/-- 수축이 3-연결이 아니면 `{x, y, z}`가 `G`를 분리하는 `z`가 있다 (Diestel의 첫 문단). -/
theorem exists_separates_of_not_threeConnected (hG : ThreeConnected G) (h5 : 5 ≤ G.support.ncard)
    (hxy : G.Adj x y) (hc : ¬ ThreeConnected (contractEdge G x y)) :
    ∃ z ∈ G.support, z ≠ x ∧ z ≠ y ∧ Separates G {x, y, z} := by
  classical
  have hsupp := support_contractEdge_of_threeConnected hG h5 hxy
  have hcut : ¬ ∀ S : Set V, S.ncard < 3 → ∀ u ∈ (contractEdge G x y).support \ S,
      ∀ v ∈ (contractEdge G x y).support \ S,
        (deleteVertices (contractEdge G x y) S).Reachable u v := by
    intro h
    refine hc ⟨?_, h⟩
    rw [hsupp]
    have h2 := Set.ncard_le_ncard_sdiff_add_ncard G.support {y}
    rw [Set.ncard_singleton] at h2
    omega
  simp only [not_forall] at hcut
  obtain ⟨S, hS, u, hu, v, hv, huv⟩ := hcut
  rw [hsupp] at hu hv
  obtain ⟨⟨hus, huy⟩, huS⟩ := hu
  obtain ⟨⟨hvs, hvy⟩, hvS⟩ := hv
  by_cases hxS : x ∈ S
  · -- `x`를 지우는 분리: `G`에서는 `S ∪ {y}`가 분리한다
    set T := (S ∪ {y}) ∩ G.support with hTdef
    have hT : ¬ (deleteVertices G T).Reachable u v := by
      rw [hTdef, deleteVertices_inter_support]
      exact fun h ↦ huv (reachable_contractEdge_of_union S h)
    have huT : u ∉ T := fun h ↦ by
      rcases h.1 with h | h
      · exact huS h
      · exact huy h
    have hvT : v ∉ T := fun h ↦ by
      rcases h.1 with h | h
      · exact hvS h
      · exact hvy h
    have hTle : T.ncard ≤ 3 := by
      have h1 : T.ncard ≤ (S ∪ {y}).ncard := Set.ncard_le_ncard Set.inter_subset_left
      have h2 := Set.ncard_union_le S {y}
      rw [Set.ncard_singleton] at h2
      omega
    have hxT : x ∈ T := ⟨Or.inl hxS, hxy.mem_support_left⟩
    have hyT : y ∈ T := ⟨Or.inr rfl, hxy.mem_support_right⟩
    have hT3 : T.ncard = 3 := by
      by_contra hne
      exact hT (hG.2 T (by omega) u ⟨hus, huT⟩ v ⟨hvs, hvT⟩)
    have hpair : ({x, y} : Set V).ncard < T.ncard := by
      rw [Set.ncard_pair hxy.ne, hT3]
      omega
    obtain ⟨z, hzT, hzxy⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hpair
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hzxy
    have hsub : ({x, y, z} : Set V) ⊆ T := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · exact hxT
      · exact hyT
      · exact hzT
    have hle : T.ncard ≤ ({x, y, z} : Set V).ncard := by
      rw [hT3, Set.ncard_eq_three.2 ⟨x, y, z, hxy.ne, fun e ↦ hzxy.1 e.symm,
        fun e ↦ hzxy.2 e.symm, rfl⟩]
    have hTeq : T = {x, y, z} := (Set.eq_of_subset_of_ncard_le hsub hle).symm
    refine ⟨z, hzT.2, hzxy.1, hzxy.2, u, ⟨hus, ?_⟩, v, ⟨hvs, ?_⟩, ?_⟩
    · rw [← hTeq]
      exact huT
    · rw [← hTeq]
      exact hvT
    · rw [← hTeq]
      exact hT
  · -- `x`를 지우지 않는 분리는 `G`에서도 분리라 3-연결성에 모순
    exfalso
    have hS' : (S \ {y}).ncard < 3 := lt_of_le_of_lt (Set.ncard_sdiff_singleton_le S y) hS
    have h := hG.2 (S \ {y}) hS' u ⟨hus, fun h ↦ huS h.1⟩ v ⟨hvs, fun h ↦ hvS h.1⟩
    exact huv (reachable_contractEdge_of_not_mem hxy.ne hxS huy hvy h)

/-- 크기 3인 분리 집합 `T`의 각 점은 `G - T`의 모든 성분에 이웃이 있다. 없으면 `T`에서 그 점을 뺀
두 점이 이미 분리한다. -/
theorem exists_adj_mem_sepComponent (hG : ThreeConnected G) {T : Set V} (hT : T.ncard = 3)
    (hsep : Separates G T) {c : V} (hc : c ∈ G.support \ T) {t : V} (ht : t ∈ T) :
    ∃ d ∈ sepComponent G T c, G.Adj t d := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  -- `C` 밖의 점 `e`
  have hout : ∃ e ∈ G.support \ T, e ∉ sepComponent G T c := by
    obtain ⟨u, hu, v, hv, huv⟩ := hsep
    by_cases huC : u ∈ sepComponent G T c
    · refine ⟨v, hv, fun hvC ↦ huv ?_⟩
      exact huC.2.symm.trans hvC.2
    · exact ⟨u, hu, huC⟩
  obtain ⟨e, he, heC⟩ := hout
  -- `T \ {t}`를 지워도 `C`를 벗어날 수 없다
  have stay : ∀ {a b : V} (p : (deleteVertices G (T \ {t})).Walk a b),
      a ∈ sepComponent G T c → b ∈ sepComponent G T c := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a a' b h p ih =>
      intro ha
      apply ih
      obtain ⟨hG', ha1, ha2⟩ := h
      have ha't : a' ≠ t := by
        rintro rfl
        exact hno a ha hG'.symm
      have ha'T : a' ∉ T := fun h' ↦ ha2 ⟨h', ha't⟩
      refine ⟨⟨hG'.mem_support_right, ha'T⟩, ha.2.trans ?_⟩
      exact Adj.reachable ⟨hG', ha.1.2, ha'T⟩
  have hT' : (T \ {t}).ncard < 3 := by
    rw [Set.ncard_sdiff_singleton_of_mem ht, hT]
    omega
  obtain ⟨p⟩ := hG.2 (T \ {t}) hT' c ⟨hc.1, fun h ↦ hc.2 h.1⟩ e ⟨he.1, fun h ↦ he.2 h.1⟩
  exact heC (stay p ⟨hc, .refl _⟩)

end Kuratowski
