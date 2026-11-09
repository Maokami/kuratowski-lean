import Kuratowski.CyclicArcs
import Kuratowski.NonPlanar
import Kuratowski.PathsBuild
import Mathlib.Data.Fin.VecNotation

/-!
# 번갈아 놓이면 `TK₃,₃` (블루프린트 `lem:TK33_of_alt`)

`x ∼ y`이고 `x`, `y`를 지나지 않는 사이클 `C` 위에 위치 `u, p, w, q`가 이 순환 순서로 있으며
(`sbtw u p w`, `sbtw w q u`) `C u`, `C w`는 `y`의 이웃, `C p`, `C q`는 `x`의 이웃이면 `G`는
`K₃,₃`의 세분을 포함한다 (`containsSubdivision_K33_of_alternating`).

두 편은 `{x, C u, C w}`와 `{y, C p, C q}`다. 경로는 변 다섯 개(`xy`, `x - C p`, `x - C q`,
`y - C u`, `y - C w`)와 `C`의 네 호다. 완전 이분 그래프의 경로 체계는 왼쪽에서 오른쪽으로 가는 경로만
주면 된다 (`SubdivisionPaths.ofBipartite`).

위치를 정수 대표의 크기순 `a < b < c < d`로 정렬하면 호는 `a → b`, `b → c`, `c → d`, `d → a`이고
`CyclicArcs`의 보조정리로 내부가 서로소이며 분기점을 피한다
(`Alternating.containsSubdivision_K33_of_sorted`). 일반 경우는 순환 순서의 네 회전으로 나눈다.
홀수 번 회전한 경우에는 `x`와 `y`의 역할을 바꾼다. `K₃,₃`의 꼭짓점이 유한하므로 `G`의 꼭짓점 타입에는
유한성을 가정하지 않는다.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*}

namespace SubdivisionPaths

variable {α β : Type*} {G : SimpleGraph V}

/-- 완전 이분 그래프의 경로 체계: 왼쪽 `a`에서 오른쪽 `b`로 가는 경로만 준다. -/
def ofBipartite (f : α ⊕ β ↪ V) (p : ∀ a b, G.Walk (f (.inl a)) (f (.inr b)))
    (hp : ∀ a b, (p a b).IsPath)
    (hint : ∀ a b, ∀ z ∈ walkInterior (p a b), z ∉ Set.range f)
    (hdisj : ∀ a b c d, (a, b) ≠ (c, d) →
      Disjoint (walkInterior (p a b)) (walkInterior (p c d))) :
    SubdivisionPaths (completeBipartiteGraph α β) G where
  branch := f
  path
    | .inl a, .inr b, _ => p a b
    | .inr b, .inl a, _ => (p a b).reverse
    | .inl _, .inl _, h => absurd h (by simp)
    | .inr _, .inr _, h => absurd h (by simp)
  isPath := by
    rintro (a | b) (a' | b') h
    · simp at h
    · exact hp a b'
    · exact (hp a' b).reverse
    · simp at h
  path_symm := by
    rintro (a | b) (a' | b') h
    · simp at h
    · rfl
    · exact (Walk.reverse_reverse _).symm
    · simp at h
  interior_not_branch := by
    rintro (a | b) (a' | b') h z hz
    · simp at h
    · exact hint a b' z hz
    · change z ∈ walkInterior (p a' b).reverse at hz
      rw [walkInterior_reverse] at hz
      exact hint a' b z hz
    · simp at h
  disjoint := by
    rintro (a | b) (a' | b') h (c | d) (c' | d') h' hne
    all_goals try (first | (simp at h; done) | (simp at h'; done))
    · exact hdisj a b' c d' fun e ↦ hne (by simp_all)
    · change Disjoint (walkInterior (p a b')) (walkInterior (p c' d).reverse)
      rw [walkInterior_reverse]
      exact hdisj a b' c' d fun e ↦ hne (by simp_all [Sym2.eq_swap])
    · change Disjoint (walkInterior (p a' b).reverse) (walkInterior (p c d'))
      rw [walkInterior_reverse]
      exact hdisj a' b c d' fun e ↦ hne (by simp_all [Sym2.eq_swap])
    · change Disjoint (walkInterior (p a' b).reverse) (walkInterior (p c' d).reverse)
      rw [walkInterior_reverse, walkInterior_reverse]
      exact hdisj a' b c' d fun e ↦ hne (by simp_all)

end SubdivisionPaths

namespace Alternating

variable {G : SimpleGraph V} {m : ℕ}

private theorem sbtw_iff_order [NeZero m] (a t b : ZMod m) :
    sbtw a t b ↔ a.val < t.val ∧ t.val < b.val ∨
      t.val < b.val ∧ b.val < a.val ∨ b.val < a.val ∧ a.val < t.val := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- 정렬된 경우: 위치가 `a.val < b.val < c.val < d.val`이고, `h₁`은 `C a`, `C c`에, `h₂`는
`C b`, `C d`에 이웃한다. 두 편은 `{h₁, C b, C d}`와 `{h₂, C a, C c}`다. -/
theorem containsSubdivision_K33_of_sorted (C : CyclicSequence G m) {h₁ h₂ : V}
    (h₁₂ : G.Adj h₁ h₂) (h₁C : h₁ ∉ Set.range C) (h₂C : h₂ ∉ Set.range C) {a b c d : ZMod m}
    (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val)
    (ha : G.Adj h₁ (C a)) (hc : G.Adj h₁ (C c)) (hb : G.Adj h₂ (C b)) (hd : G.Adj h₂ (C d)) :
    ContainsSubdivision G K33 := by
  classical
  have : NeZero m := C.neZero
  have hne : ∀ {s t : ZMod m}, s.val < t.val → s ≠ t := fun h e ↦ by
    rw [e] at h
    exact lt_irrefl _ h
  have h1t : ∀ t, h₁ ≠ C t := fun t e ↦ h₁C ⟨t, e.symm⟩
  have h2t : ∀ t, h₂ ≠ C t := fun t e ↦ h₂C ⟨t, e.symm⟩
  have nab := hne hab
  have nbc := hne hbc
  have ncd := hne hcd
  have nac := hne (hab.trans hbc)
  have nbd := hne (hbc.trans hcd)
  have nad := hne (hab.trans (hbc.trans hcd))
  let L : Fin 3 → V := ![h₁, C b, C d]
  let R : Fin 3 → V := ![h₂, C a, C c]
  have hg : Function.Injective (Sum.elim L R) := by
    rintro (i | i) (j | j) e <;> fin_cases i <;> fin_cases j <;>
      simp_all [L, R, h₁₂.ne, h₁₂.ne.symm, Ne.symm]
  let f : Fin 3 ⊕ Fin 3 ↪ V := ⟨Sum.elim L R, hg⟩
  -- 네 호의 내부와 분기점
  have avoid : ∀ {s t : ZMod m} (hst : s.val ≤ t.val),
      (∀ r ∈ [a, b, c, d], r.val ≤ s.val ∨ t.val ≤ r.val) →
      ∀ z ∈ walkInterior (C.arc s t), z ∉ Set.range f := by
    intro s t hst hr z hz
    rintro ⟨i | i, rfl⟩ <;> fin_cases i
    · exact C.not_mem_arc_support_of_not_mem_range h₁C _ _ hz.1
    · exact C.not_mem_arc_interior_of_le s t b hst (hr b (by simp)) hz
    · exact C.not_mem_arc_interior_of_le s t d hst (hr d (by simp)) hz
    · exact C.not_mem_arc_support_of_not_mem_range h₂C _ _ hz.1
    · exact C.not_mem_arc_interior_of_le s t a hst (hr a (by simp)) hz
    · exact C.not_mem_arc_interior_of_le s t c hst (hr c (by simp)) hz
  have avoidW : ∀ z ∈ walkInterior (C.arc d a), z ∉ Set.range f := by
    intro z hz
    rintro ⟨i | i, rfl⟩ <;> fin_cases i
    · exact C.not_mem_arc_support_of_not_mem_range h₁C _ _ hz.1
    · exact C.not_mem_arc_interior_wrap a d b hab.le (hbc.trans hcd).le hz
    · exact C.not_mem_arc_interior_wrap a d d (hab.trans (hbc.trans hcd)).le le_rfl hz
    · exact C.not_mem_arc_support_of_not_mem_range h₂C _ _ hz.1
    · exact C.not_mem_arc_interior_wrap a d a le_rfl (hab.trans (hbc.trans hcd)).le hz
    · exact C.not_mem_arc_interior_wrap a d c (hab.trans hbc).le hcd.le hz
  have hr : ∀ {s t : ZMod m}, (∀ r : ZMod m, r = a ∨ r = b ∨ r = c ∨ r = d →
      r.val ≤ s.val ∨ t.val ≤ r.val) → ∀ r ∈ [a, b, c, d], r.val ≤ s.val ∨ t.val ≤ r.val := by
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact h r hr
  have A11 := avoid hab.le (hr (by rintro r (rfl | rfl | rfl | rfl) <;> omega))
  have A12 := avoid hbc.le (hr (by rintro r (rfl | rfl | rfl | rfl) <;> omega))
  have A22 := avoid hcd.le (hr (by rintro r (rfl | rfl | rfl | rfl) <;> omega))
  have D1 : Disjoint (walkInterior (C.arc a b)) (walkInterior (C.arc b c)) :=
    C.disjoint_arc_interiors_of_le a b b c hab.le le_rfl hbc.le
  have D2 : Disjoint (walkInterior (C.arc a b)) (walkInterior (C.arc c d)) :=
    C.disjoint_arc_interiors_of_le a b c d hab.le hbc.le hcd.le
  have D3 : Disjoint (walkInterior (C.arc b c)) (walkInterior (C.arc c d)) :=
    C.disjoint_arc_interiors_of_le b c c d hbc.le le_rfl hcd.le
  have D4 : Disjoint (walkInterior (C.arc d a)) (walkInterior (C.arc b c)) :=
    C.disjoint_arc_interiors_wrap a b c d hab.le hbc.le hcd.le
  have D5 : Disjoint (walkInterior (C.arc d a)) (walkInterior (C.arc a b)) :=
    C.disjoint_arc_interiors_wrap a a b d le_rfl hab.le (hbc.trans hcd).le
  have D6 : Disjoint (walkInterior (C.arc d a)) (walkInterior (C.arc c d)) :=
    C.disjoint_arc_interiors_wrap a c d d (hab.trans hbc).le hcd.le le_rfl
  -- 경로
  let posL : Fin 3 → ZMod m := ![a, b, d]
  let posR : Fin 3 → ZMod m := ![a, a, c]
  have hposL : ∀ i : Fin 3, i ≠ 0 → C (posL i) = f (.inl i) := by
    intro i hi
    fin_cases i <;> first | rfl | exact absurd rfl hi
  have hposR : ∀ j : Fin 3, j ≠ 0 → C (posR j) = f (.inr j) := by
    intro j hj
    fin_cases j <;> first | rfl | exact absurd rfl hj
  have hadj : ∀ i j : Fin 3, (i = 0 ∨ j = 0) → G.Adj (f (.inl i)) (f (.inr j)) := by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals first
      | exact h₁₂
      | exact ha
      | exact hc
      | exact hb.symm
      | exact hd.symm
      | (exfalso; revert h; decide)
  let p : ∀ i j : Fin 3, G.Walk (f (.inl i)) (f (.inr j)) := fun i j ↦
    if h0 : i = 0 ∨ j = 0 then Walk.cons (hadj i j h0) Walk.nil
    else if i ≠ j then
      (C.arc (posL i) (posR j)).copy (hposL i fun e ↦ h0 (Or.inl e))
        (hposR j fun e ↦ h0 (Or.inr e))
    else (C.arc (posR j) (posL i)).reverse.copy (hposL i fun e ↦ h0 (Or.inl e))
        (hposR j fun e ↦ h0 (Or.inr e))
  have hE : ∀ i j, (i = 0 ∨ j = 0) → walkInterior (p i j) = ∅ := by
    intro i j h0
    simp only [p, h0, ↓reduceDIte, walkInterior_cons_nil]
  have hF : ∀ i j, ¬(i = 0 ∨ j = 0) → i ≠ j →
      walkInterior (p i j) = walkInterior (C.arc (posL i) (posR j)) := by
    intro i j h0 hij
    simp only [p, h0, hij, ↓reduceDIte, ne_eq, not_false_eq_true, ↓reduceIte, walkInterior_copy]
  have hB : ∀ i j, ¬(i = 0 ∨ j = 0) → i = j →
      walkInterior (p i j) = walkInterior (C.arc (posR j) (posL i)) := by
    intro i j h0 hij
    subst hij
    simp only [p, h0, ↓reduceDIte, ne_eq, not_true_eq_false, ↓reduceIte, walkInterior_copy,
      walkInterior_reverse]
  have I11 : walkInterior (p 1 1) = walkInterior (C.arc a b) := hB 1 1 (by decide) rfl
  have I12 : walkInterior (p 1 2) = walkInterior (C.arc b c) := hF 1 2 (by decide) (by decide)
  have I21 : walkInterior (p 2 1) = walkInterior (C.arc d a) := hF 2 1 (by decide) (by decide)
  have I22 : walkInterior (p 2 2) = walkInterior (C.arc c d) := hB 2 2 (by decide) rfl
  have h3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  refine (SubdivisionPaths.ofBipartite f p ?_ ?_ ?_).containsSubdivision_of_finite
  · intro i j
    simp only [p]
    split_ifs with h0
    · rw [Walk.cons_isPath_iff]
      exact ⟨Walk.IsPath.nil, by simp⟩
    · rw [Walk.isPath_copy]
      exact C.arc_isPath _ _
    · rw [Walk.isPath_copy, Walk.isPath_reverse_iff]
      exact C.arc_isPath _ _
  · intro i j z hz
    by_cases h0 : i = 0 ∨ j = 0
    · rw [hE i j h0] at hz
      exact hz.elim
    rcases h3 i with rfl | rfl | rfl <;> rcases h3 j with rfl | rfl | rfl
    all_goals first
      | exact (h0 (by decide)).elim
      | (rw [I11] at hz; exact A11 z hz)
      | (rw [I12] at hz; exact A12 z hz)
      | (rw [I21] at hz; exact avoidW z hz)
      | (rw [I22] at hz; exact A22 z hz)
  · intro i j k l hne
    by_cases h0 : i = 0 ∨ j = 0
    · rw [hE i j h0]
      exact Set.empty_disjoint _
    by_cases h1 : k = 0 ∨ l = 0
    · rw [hE k l h1]
      exact Set.disjoint_empty _
    rcases h3 i with rfl | rfl | rfl <;> rcases h3 j with rfl | rfl | rfl <;>
      rcases h3 k with rfl | rfl | rfl <;> rcases h3 l with rfl | rfl | rfl
    all_goals try first
      | exact (h0 (by decide)).elim
      | exact (h1 (by decide)).elim
      | exact absurd rfl hne
    all_goals simp only [I11, I12, I21, I22]
    all_goals first
      | exact D1
      | exact D1.symm
      | exact D2
      | exact D2.symm
      | exact D3
      | exact D3.symm
      | exact D4
      | exact D4.symm
      | exact D5
      | exact D5.symm
      | exact D6
      | exact D6.symm

end Alternating

/-- 블루프린트 `lem:TK33_of_alt`: `x ∼ y`이고 `x`, `y`를 지나지 않는 사이클 `C` 위에 위치 `u, p, w, q`가
이 순환 순서로 있으며(`sbtw u p w`, `sbtw w q u`), `C u`, `C w`는 `y`의 이웃이고 `C p`, `C q`는
`x`의 이웃이면 `G`는 `K₃,₃`의 세분을 포함한다. -/
theorem containsSubdivision_K33_of_alternating {G : SimpleGraph V} {m : ℕ}
    (C : CyclicSequence G m) {x y : V} (hxy : G.Adj x y) (hxC : x ∉ Set.range C)
    (hyC : y ∉ Set.range C) {u p w q : ZMod m} (hupw : sbtw u p w) (hwqu : sbtw w q u)
    (hu : G.Adj y (C u)) (hw : G.Adj y (C w)) (hp : G.Adj x (C p)) (hq : G.Adj x (C q)) :
    ContainsSubdivision G K33 := by
  have : NeZero m := C.neZero
  rw [Alternating.sbtw_iff_order] at hupw hwqu
  have sorted := @Alternating.containsSubdivision_K33_of_sorted V G m C
  rcases hupw with h1 | h1 | h1 <;> rcases hwqu with h2 | h2 | h2
  all_goals first
    | exact sorted hxy.symm hyC hxC (a := u) (b := p) (c := w) (d := q)
        (by omega) (by omega) (by omega) hu hw hp hq
    | exact sorted hxy hxC hyC (a := p) (b := w) (c := q) (d := u)
        (by omega) (by omega) (by omega) hp hq hw hu
    | exact sorted hxy.symm hyC hxC (a := w) (b := q) (c := u) (d := p)
        (by omega) (by omega) (by omega) hw hu hq hp
    | exact sorted hxy hxC hyC (a := q) (b := u) (c := p) (d := w)
        (by omega) (by omega) (by omega) hq hp hu hw

end Kuratowski
