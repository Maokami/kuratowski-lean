import Kuratowski.CyclicArcs
import Kuratowski.NonPlanar
import Kuratowski.PathsBuild
import Mathlib.Data.Fin.VecNotation

/-!
# 공통 이웃 셋이면 `TK₅` (블루프린트 `lem:TK5_of_common`)

`x ∼ y`이고 `x`, `y`를 지나지 않는 사이클 `C`의 서로 다른 세 위치 `i`, `j`, `k`가 `x`와 `y`의 공통
이웃이면 `G`는 `K₅`의 세분을 포함한다 (`containsSubdivision_K5_of_three_common`).

분기점은 `x, y, C i, C j, C k`다. `x`나 `y`를 끝점으로 하는 변은 `G`의 한 변이고, 세 공통 이웃 사이의
변은 `C`의 세 호다. 위치를 `i.val < j.val < k.val`로 정렬하면 호는 `i → j`, `j → k`, `k → i`이고,
`CyclicArcs`의 보조정리로 내부가 서로소이며 분기점을 피한다. 일반 경우는 세 위치의 여섯 가지 순서로
나눈다. `K₅`의 꼭짓점이 유한하므로 `G`의 꼭짓점 타입에는 유한성을 가정하지 않는다.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*}

/-! ### 공통 이웃 셋이면 `TK₅` -/

namespace CommonNeighbors

variable {G : SimpleGraph V} {m : ℕ}

/-- 정렬된 경우: 위치가 `i.val < j.val < k.val`. -/
theorem containsSubdivision_K5_of_sorted (C : CyclicSequence G m) {x y : V} (hxy : G.Adj x y)
    (hxC : x ∉ Set.range C) (hyC : y ∉ Set.range C) {i j k : ZMod m}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    (hi : G.Adj x (C i) ∧ G.Adj y (C i)) (hj : G.Adj x (C j) ∧ G.Adj y (C j))
    (hk : G.Adj x (C k) ∧ G.Adj y (C k)) : ContainsSubdivision G K5 := by
  classical
  have : NeZero m := C.neZero
  have hne_ij : i ≠ j := fun e ↦ by rw [e] at hij; exact lt_irrefl _ hij
  have hne_jk : j ≠ k := fun e ↦ by rw [e] at hjk; exact lt_irrefl _ hjk
  have hne_ik : i ≠ k := fun e ↦ by rw [e] at hij; exact lt_irrefl _ (hij.trans hjk)
  have hxt : ∀ t, x ≠ C t := fun t e ↦ hxC ⟨t, e.symm⟩
  have hyt : ∀ t, y ≠ C t := fun t e ↦ hyC ⟨t, e.symm⟩
  let g : Fin 5 → V := ![x, y, C i, C j, C k]
  have hg : Function.Injective g := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [g, hxy.ne, hxy.ne.symm, Ne.symm]
  let f : Fin 5 ↪ V := ⟨g, hg⟩
  let pos : Fin 5 → ZMod m := ![i, i, i, j, k]
  have hpos : ∀ c : Fin 5, ¬ c.val < 2 → C (pos c) = f c := by
    intro c hc
    fin_cases c <;> first | rfl | (simp at hc)
  have hadj : ∀ a b : Fin 5, a.val < 2 → a < b → G.Adj (f a) (f b) := by
    intro a b ha hab
    fin_cases a <;> fin_cases b <;> simp_all [f, g, Fin.lt_def]
  -- 세 호의 내부
  have A1 : ∀ c, f c ∉ walkInterior (C.arc i j) := by
    intro c
    fin_cases c
    · exact fun hz ↦ C.not_mem_arc_support_of_not_mem_range hxC _ _ hz.1
    · exact fun hz ↦ C.not_mem_arc_support_of_not_mem_range hyC _ _ hz.1
    · exact C.not_mem_arc_interior_of_le i j i hij.le (Or.inl le_rfl)
    · exact C.not_mem_arc_interior_of_le i j j hij.le (Or.inr le_rfl)
    · exact C.not_mem_arc_interior_of_le i j k hij.le (Or.inr hjk.le)
  have A2 : ∀ c, f c ∉ walkInterior (C.arc j k) := by
    intro c
    fin_cases c
    · exact fun hz ↦ C.not_mem_arc_support_of_not_mem_range hxC _ _ hz.1
    · exact fun hz ↦ C.not_mem_arc_support_of_not_mem_range hyC _ _ hz.1
    · exact C.not_mem_arc_interior_of_le j k i hjk.le (Or.inl hij.le)
    · exact C.not_mem_arc_interior_of_le j k j hjk.le (Or.inl le_rfl)
    · exact C.not_mem_arc_interior_of_le j k k hjk.le (Or.inr le_rfl)
  have A3 : ∀ c, f c ∉ walkInterior (C.arc k i) := by
    intro c
    fin_cases c
    · exact fun hz ↦ C.not_mem_arc_support_of_not_mem_range hxC _ _ hz.1
    · exact fun hz ↦ C.not_mem_arc_support_of_not_mem_range hyC _ _ hz.1
    · exact C.not_mem_arc_interior_wrap i k i le_rfl (hij.trans hjk).le
    · exact C.not_mem_arc_interior_wrap i k j hij.le hjk.le
    · exact C.not_mem_arc_interior_wrap i k k (hij.trans hjk).le le_rfl
  have D12 : Disjoint (walkInterior (C.arc i j)) (walkInterior (C.arc j k)) :=
    C.disjoint_arc_interiors_of_le i j j k hij.le le_rfl hjk.le
  have D32 : Disjoint (walkInterior (C.arc k i)) (walkInterior (C.arc j k)) :=
    C.disjoint_arc_interiors_wrap i j k k hij.le hjk.le le_rfl
  have D31 : Disjoint (walkInterior (C.arc k i)) (walkInterior (C.arc i j)) :=
    C.disjoint_arc_interiors_wrap i i j k le_rfl hij.le hjk.le
  -- 경로
  let p : ∀ a b : Fin 5, a < b → K5.Adj a b → G.Walk (f a) (f b) := fun a b hab _ ↦
    if ha : a.val < 2 then Walk.cons (hadj a b ha hab) Walk.nil
    else if hb : b.val = a.val + 1 then
      (C.arc (pos a) (pos b)).copy (hpos a ha) (hpos b (by omega))
    else (C.arc (pos b) (pos a)).reverse.copy (hpos a ha) (hpos b (by omega))
  have hcase : ∀ a b : Fin 5, a < b → ¬ a.val < 2 →
      (a = 2 ∧ b = 3) ∨ (a = 2 ∧ b = 4) ∨ (a = 3 ∧ b = 4) := by
    intro a b hab ha
    fin_cases a <;> fin_cases b <;> simp_all [Fin.lt_def]
  have hpint : ∀ a b (hab : a < b) (h : K5.Adj a b), walkInterior (p a b hab h) =
      if a.val < 2 then ∅ else if b.val = a.val + 1 then walkInterior (C.arc (pos a) (pos b))
      else walkInterior (C.arc (pos b) (pos a)) := by
    intro a b hab h
    simp only [p]
    split_ifs <;> simp
  have hint3 : ∀ a b : Fin 5, a < b → ¬ a.val < 2 → ∀ z, z ∈ (if b.val = a.val + 1 then
      walkInterior (C.arc (pos a) (pos b)) else walkInterior (C.arc (pos b) (pos a))) →
      z ∉ Set.range f := by
    intro a b hab ha z hz
    rintro ⟨c, rfl⟩
    rcases hcase a b hab ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact A1 c hz
    · exact A3 c hz
    · exact A2 c hz
  have P : SubdivisionPaths K5 G := by
    refine SubdivisionPaths.ofLT f p ?_ ?_ ?_
    · intro a b hab h
      simp only [p]
      split_ifs with ha hb
      · rw [Walk.cons_isPath_iff]
        exact ⟨Walk.IsPath.nil, by simpa using f.injective.ne hab.ne⟩
      · rw [Walk.isPath_copy]
        exact C.arc_isPath _ _
      · rw [Walk.isPath_copy, Walk.isPath_reverse_iff]
        exact C.arc_isPath _ _
    · intro a b hab h z hz
      rw [hpint a b hab h] at hz
      by_cases ha : a.val < 2
      · simp [ha] at hz
      · simp only [ha, ↓reduceIte] at hz
        exact hint3 a b hab ha z hz
    · intro a b hab h c d hcd h' hne
      rw [hpint a b hab h, hpint c d hcd h']
      by_cases ha : a.val < 2
      · simp only [ha, ↓reduceIte]
        exact Set.empty_disjoint _
      by_cases hc : c.val < 2
      · simp only [hc, ↓reduceIte]
        exact Set.disjoint_empty _
      simp only [ha, hc, ↓reduceIte]
      · rcases hcase a b hab ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hcase c d hcd hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        all_goals first
          | exact absurd rfl hne
          | exact D12
          | exact D12.symm
          | exact D32
          | exact D32.symm
          | exact D31
          | exact D31.symm
  exact P.containsSubdivision_of_finite

end CommonNeighbors

/-- 블루프린트 `lem:TK5_of_common`: `x ∼ y`이고 `x`, `y`를 지나지 않는 사이클 `C`의 서로 다른 세
위치가 `x`와 `y`의 공통 이웃이면 `G`는 `K₅`의 세분을 포함한다. -/
theorem containsSubdivision_K5_of_three_common {G : SimpleGraph V} {m : ℕ}
    (C : CyclicSequence G m) {x y : V} (hxy : G.Adj x y) (hxC : x ∉ Set.range C)
    (hyC : y ∉ Set.range C) {i j k : ZMod m} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : G.Adj x (C i) ∧ G.Adj y (C i)) (hj : G.Adj x (C j) ∧ G.Adj y (C j))
    (hk : G.Adj x (C k) ∧ G.Adj y (C k)) : ContainsSubdivision G K5 := by
  have : NeZero m := C.neZero
  have vij : i.val ≠ j.val := fun e ↦ hij (ZMod.val_injective m e)
  have vik : i.val ≠ k.val := fun e ↦ hik (ZMod.val_injective m e)
  have vjk : j.val ≠ k.val := fun e ↦ hjk (ZMod.val_injective m e)
  have sorted := @CommonNeighbors.containsSubdivision_K5_of_sorted V G m C x y hxy hxC hyC
  rcases Nat.lt_or_gt_of_ne vij with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne vik with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne vjk with h3 | h3
  all_goals first
    | exact sorted (i := i) (j := j) (k := k) (by omega) (by omega) hi hj hk
    | exact sorted (i := i) (j := k) (k := j) (by omega) (by omega) hi hk hj
    | exact sorted (i := j) (j := i) (k := k) (by omega) (by omega) hj hi hk
    | exact sorted (i := j) (j := k) (k := i) (by omega) (by omega) hj hk hi
    | exact sorted (i := k) (j := i) (k := j) (by omega) (by omega) hk hi hj
    | exact sorted (i := k) (j := j) (k := i) (by omega) (by omega) hk hj hi

end Kuratowski
