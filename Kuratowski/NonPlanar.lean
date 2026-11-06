import Kuratowski.Basic
import Kuratowski.Components

/-!
# 변 개수 상한과 `K₅`, `K₃,₃`의 비평면성

차수 1인 꼭짓점이 없으면 면의 길이가 3 이상이므로 (이분 그래프면 4 이상) 면 수를 변 수로
위에서 누를 수 있다. (차수 1인 꼭짓점이 있으면 길이 2인 면이 생긴다. 예: `K₂`.)
오일러 공식 `V - E + F = 2c`와 "고립점은 각각 성분 하나이고, 변이 있으면 성분이 하나 더 있다"
(`c ≥ I + 1`)를 합치면, 변이 하나 이상 있고 차수 1인 꼭짓점이 없는 평면 그래프에 대해

* `E + 6 + 3I ≤ 3V`
* 이분 그래프이면 `E + 4 + 2I ≤ 2V`

를 얻는다 (`I`는 고립점 수). 고립점을 허용하는 것은 `K₅`, `K₃,₃`를 더 큰 꼭짓점 집합 안에
넣은 그래프(`K.map f`)에도 바로 쓰기 위해서다. `K₅`는 `V - I = 5`, `E = 10`이라 첫 부등식을,
`K₃,₃`는 `V - I = 6`, `E = 9`라 둘째 부등식을 어긴다.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- 차수 1인 꼭짓점이 없다: 변 `uv`의 끝 `v`에는 `u` 말고 다른 이웃이 있다. -/
def NoLeaf (G : SimpleGraph V) : Prop := ∀ u v, G.Adj u v → ∃ z, G.Adj v z ∧ z ≠ u

namespace RotationSystem

variable (R : RotationSystem G)

/-- 차수 1인 꼭짓점이 없으면 모든 면의 길이가 3 이상이므로 `3F ≤ 2E`. -/
lemma three_mul_orbitCount_le [Finite V] (h : NoLeaf G) :
    3 * orbitCount R.facePerm ≤ 2 * G.edgeSet.ncard := by
  rw [← card_dart_eq]
  refine mul_orbitCount_le R.facePerm 3 fun d k hk hk3 => ?_
  obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
  · simpa using R.facePerm_ne_self d
  · obtain ⟨z, hz, hne⟩ := h _ _ d.adj
    rw [pow_two, Equiv.Perm.mul_apply]
    exact R.facePerm_facePerm_ne_self d hz hne

private lemma fin_two_triangle : ∀ a b c : Fin 2, a ≠ b → b ≠ c → c ≠ a → False := by decide

/-- 이분 그래프에서는 면을 따라 걸을 때 두 색이 번갈아 나오므로 길이 3인 면도 없다. -/
lemma facePerm_pow_three_ne_self (hbip : G.IsBipartite) (d : G.Dart) :
    (R.facePerm ^ 3) d ≠ d := by
  obtain ⟨C⟩ := hbip
  intro h
  have h3 : (R.facePerm (R.facePerm d)).snd = d.fst := by
    have := congrArg (fun x : G.Dart => x.fst) h
    simpa [pow_succ, Equiv.Perm.mul_apply, -facePerm_apply] using this
  have e1 := C.valid d.adj
  have e2 := C.valid (R.facePerm d).adj
  have e3 := C.valid (R.facePerm (R.facePerm d)).adj
  simp only [facePerm_fst] at e2 e3
  rw [h3] at e3
  exact fin_two_triangle _ _ _ e1 e2 e3

/-- 차수 1인 꼭짓점이 없는 이분 그래프에서는 모든 면의 길이가 4 이상이므로 `4F ≤ 2E`. -/
lemma four_mul_orbitCount_le [Finite V] (h : NoLeaf G) (hbip : G.IsBipartite) :
    4 * orbitCount R.facePerm ≤ 2 * G.edgeSet.ncard := by
  rw [← card_dart_eq]
  refine mul_orbitCount_le R.facePerm 4 fun d k hk hk4 => ?_
  obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  · simpa using R.facePerm_ne_self d
  · obtain ⟨z, hz, hne⟩ := h _ _ d.adj
    rw [pow_two, Equiv.Perm.mul_apply]
    exact R.facePerm_facePerm_ne_self d hz hne
  · exact R.facePerm_pow_three_ne_self hbip d

end RotationSystem

variable [Finite V]

/-- 변이 있고 차수 1인 꼭짓점이 없는 평면 그래프는 `E + 6 + 3I ≤ 3V`를 만족한다
(`I`는 고립점 수). 고립점이 없으면 익숙한 `E ≤ 3V - 6`이다. -/
theorem IsPlanar.edge_bound (hP : IsPlanar G) (h : NoLeaf G) {u v : V} (huv : G.Adj u v) :
    G.edgeSet.ncard + 6 + 3 * {w | G.IsIsolated w}.ncard ≤ 3 * Nat.card V := by
  obtain ⟨R, hR⟩ := hP
  have hF := R.three_mul_orbitCount_le h
  have hc := ncard_isolated_add_one_le G huv
  unfold RotationSystem.eulerChar RotationSystem.numFaces at hR
  push_cast at hR
  omega

/-- 변이 있고 차수 1인 꼭짓점이 없는 이분 평면 그래프는 `E + 4 + 2I ≤ 2V`를 만족한다.
고립점이 없으면 익숙한 `E ≤ 2V - 4`이다. -/
theorem IsPlanar.edge_bound_of_isBipartite (hP : IsPlanar G) (h : NoLeaf G)
    (hbip : G.IsBipartite) {u v : V} (huv : G.Adj u v) :
    G.edgeSet.ncard + 4 + 2 * {w | G.IsIsolated w}.ncard ≤ 2 * Nat.card V := by
  obtain ⟨R, hR⟩ := hP
  have hF := R.four_mul_orbitCount_le h hbip
  have hc := ncard_isolated_add_one_le G huv
  unfold RotationSystem.eulerChar RotationSystem.numFaces at hR
  push_cast at hR
  omega

/-! ## 꼭짓점 집합을 넓힌 그래프 `K.map f` -/

section Map

variable {W : Type*} [Finite W] {K : SimpleGraph W} (f : W ↪ V)

omit [Finite V] [Finite W] in
lemma NoLeaf.map (h : NoLeaf K) : NoLeaf (K.map f) := by
  intro u v huv
  obtain ⟨a, b, hab, rfl, rfl⟩ := (map_adj f K u v).1 huv
  obtain ⟨z, hz, hne⟩ := h a b hab
  exact ⟨f z, (map_adj f K _ _).2 ⟨b, z, hz, rfl, rfl⟩, fun h' => hne (f.injective h')⟩

omit [Finite V] [Finite W] in
lemma IsBipartite.map [Nonempty W] (h : K.IsBipartite) : (K.map f).IsBipartite := by
  classical
  let g : V → W := fun v => if hv : ∃ a, f a = v then hv.choose else Classical.arbitrary W
  have hg : ∀ a, g (f a) = a := fun a => by
    have hv : ∃ a', f a' = f a := ⟨a, rfl⟩
    simp only [g, dite_eq_left hv]
    exact f.injective hv.choose_spec
  let φ : K.map f →g K :=
    { toFun := g
      map_rel' := by
        intro u v huv
        obtain ⟨a, b, hab, rfl, rfl⟩ := (map_adj f K u v).1 huv
        simpa [hg] using hab }
  exact Colorable.of_hom φ h

/-- `K`에 고립점도 차수 1인 꼭짓점도 없으면, `K.map f`가 평면 그래프일 때
`|E(K)| + 6 ≤ 3 |W|`. -/
lemma edge_bound_map (h : NoLeaf K) (hK : ∀ a, ¬ K.IsIsolated a) {a b : W} (hab : K.Adj a b)
    (hP : IsPlanar (K.map f)) : K.edgeSet.ncard + 6 ≤ 3 * Nat.card W := by
  have := hP.edge_bound (h.map f) (u := f a) (v := f b) ((map_adj f K _ _).2 ⟨a, b, hab, rfl, rfl⟩)
  have hI := ncard_isolated_map K f hK
  rw [ncard_edgeSet_map] at this
  omega

lemma edge_bound_map_of_isBipartite [Nonempty W] (h : NoLeaf K) (hbip : K.IsBipartite)
    (hK : ∀ a, ¬ K.IsIsolated a) {a b : W} (hab : K.Adj a b) (hP : IsPlanar (K.map f)) :
    K.edgeSet.ncard + 4 ≤ 2 * Nat.card W := by
  have := hP.edge_bound_of_isBipartite (h.map f) (hbip.map f) (u := f a) (v := f b)
    ((map_adj f K _ _).2 ⟨a, b, hab, rfl, rfl⟩)
  have hI := ncard_isolated_map K f hK
  rw [ncard_edgeSet_map] at this
  omega

end Map

end Kuratowski

/-! ## `K₅`와 `K₃,₃` -/

namespace Kuratowski

open SimpleGraph

/-- 완전 그래프 `K₅`. -/
abbrev K5 : SimpleGraph (Fin 5) := ⊤

/-- 완전 이분 그래프 `K₃,₃`. -/
abbrev K33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

instance : DecidableRel K33.Adj := fun v w =>
  decidable_of_iff _ (Iff.of_eq (completeBipartiteGraph_adj (Fin 3) (Fin 3) v w).symm)

lemma K5_noLeaf : NoLeaf K5 := by
  unfold NoLeaf
  decide

lemma K33_noLeaf : NoLeaf K33 := by
  unfold NoLeaf
  decide +kernel

lemma K5_not_isolated (a : Fin 5) : ¬ K5.IsIsolated a := by
  unfold IsIsolated
  revert a
  decide

lemma K33_not_isolated (a : Fin 3 ⊕ Fin 3) : ¬ K33.IsIsolated a := by
  unfold IsIsolated
  revert a
  decide +kernel

lemma K5_ncard_edgeSet : K5.edgeSet.ncard = 10 := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two]
  rfl

lemma K33_ncard_edgeSet : K33.edgeSet.ncard = 9 := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  decide +kernel

/-- `K₅`를 어떤 꼭짓점 집합에 넣어도 평면 그래프가 아니다. -/
theorem K5_map_not_isPlanar {V : Type*} [Finite V] (f : Fin 5 ↪ V) : ¬ IsPlanar (K5.map f) := by
  intro h
  have := edge_bound_map f K5_noLeaf K5_not_isolated (a := 0) (b := 1) (by decide) h
  rw [K5_ncard_edgeSet, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

/-- `K₃,₃`를 어떤 꼭짓점 집합에 넣어도 평면 그래프가 아니다. -/
theorem K33_map_not_isPlanar {V : Type*} [Finite V] (f : Fin 3 ⊕ Fin 3 ↪ V) :
    ¬ IsPlanar (K33.map f) := by
  intro h
  have := edge_bound_map_of_isBipartite f K33_noLeaf (IsBipartite.completeBipartiteGraph _ _)
    K33_not_isolated (a := .inl 0) (b := .inr 0) (by decide +kernel) h
  rw [K33_ncard_edgeSet, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin] at this
  omega

/-- **`K₅`는 평면 그래프가 아니다.** -/
theorem K5_not_isPlanar : ¬ IsPlanar K5 := by
  intro h
  have := h.edge_bound K5_noLeaf (u := 0) (v := 1) (by decide)
  have hI : {w | K5.IsIsolated w}.ncard = 0 := by
    rw [Set.ncard_eq_zero]
    exact Set.eq_empty_of_forall_notMem K5_not_isolated
  rw [K5_ncard_edgeSet, hI, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

/-- **`K₃,₃`는 평면 그래프가 아니다.** -/
theorem K33_not_isPlanar : ¬ IsPlanar K33 := by
  intro h
  have := h.edge_bound_of_isBipartite K33_noLeaf (IsBipartite.completeBipartiteGraph _ _)
    (u := .inl 0) (v := .inr 0) (by decide +kernel)
  have hI : {w | K33.IsIsolated w}.ncard = 0 := by
    rw [Set.ncard_eq_zero]
    exact Set.eq_empty_of_forall_notMem K33_not_isolated
  rw [K33_ncard_edgeSet, hI, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin] at this
  omega

end Kuratowski
