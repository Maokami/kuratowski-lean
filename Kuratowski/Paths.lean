import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# 세분의 경로 체계

블루프린트 정의 `def:paths`. 그래프 `K`(꼭짓점 `W`)의 `G`(꼭짓점 `V`) 안 경로 체계는
분기점 `branch : W ↪ V`와 `K`의 변 `ab`마다 `G`의 경로 `branch a → branch b`로 이루어진다.

* 반대 방향의 경로는 뒤집은 경로다 (`path_symm`, 블루프린트의 `P_ba = P_ab⁻¹`).
* 경로의 내부 꼭짓점은 분기점이 아니다 (`interior_not_branch`).
* 서로 다른 두 변(`Sym2`로 비교)의 경로는 내부 꼭짓점을 공유하지 않는다 (`disjoint`).

`K`에서 인접하지 않는 두 꼭짓점에 대해서는 아무것도 요구하지 않는다. 그래서 `G`에 분기점 사이의
다른 변(현)이 있어도 된다. 귀납적인 세분 정의(`IsSubdivision`)와의 동치(`thm:paths_iff`)는
`PathsSubdivision.lean`(정방향)과 `SubdivisionOfPaths.lean`(역방향, 유한한 `V`)에 있다.
-/

namespace Kuratowski

open SimpleGraph

variable {V W : Type*}

/-! ### 걸음의 내부 꼭짓점 -/

/-- 걸음의 내부 꼭짓점: 지나는 꼭짓점 가운데 두 끝점이 아닌 것. 경로에서는 끝점을 뺀 나머지다. -/
def walkInterior {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

theorem mem_walkInterior {G : SimpleGraph V} {u v x : V} {p : G.Walk u v} :
    x ∈ walkInterior p ↔ x ∈ p.support ∧ x ≠ u ∧ x ≠ v := Iff.rfl

/-- 걸음을 뒤집어도 내부 꼭짓점은 같다. -/
@[simp] theorem walkInterior_reverse {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    walkInterior p.reverse = walkInterior p := by
  ext x
  simp only [mem_walkInterior, Walk.support_reverse, List.mem_reverse]
  tauto

/-- 한 변짜리 걸음에는 내부 꼭짓점이 없다. -/
@[simp] theorem walkInterior_cons_nil {G : SimpleGraph V} {u v : V} (h : G.Adj u v) :
    walkInterior (Walk.cons h Walk.nil) = ∅ := by
  ext x
  simp only [mem_walkInterior, Walk.support_cons, Walk.support_nil, List.mem_cons,
    List.not_mem_nil, or_false, Set.mem_empty_iff_false, iff_false]
  tauto

/-! ### 경로 체계 -/

/-- `K`(꼭짓점 `W`)의 `G`(꼭짓점 `V`) 안 경로 체계 (블루프린트 `def:paths`). -/
structure SubdivisionPaths (K : SimpleGraph W) (G : SimpleGraph V) where
  /-- 분기점: `K`의 꼭짓점을 `G`의 서로 다른 꼭짓점에 놓는다. -/
  branch : W ↪ V
  /-- `K`의 변 `ab`마다 `G`에서 `branch a`부터 `branch b`까지 가는 걸음. -/
  path : ∀ a b, K.Adj a b → G.Walk (branch a) (branch b)
  /-- 각 걸음은 경로다 (꼭짓점을 반복하지 않는다). -/
  isPath : ∀ a b (h : K.Adj a b), (path a b h).IsPath
  /-- 반대 방향의 경로는 뒤집은 경로다. -/
  path_symm : ∀ a b (h : K.Adj a b), path b a h.symm = (path a b h).reverse
  /-- 경로의 내부 꼭짓점은 분기점이 아니다. -/
  interior_not_branch :
    ∀ a b (h : K.Adj a b), ∀ x ∈ walkInterior (path a b h), x ∉ Set.range branch
  /-- 서로 다른 두 변의 경로는 내부 꼭짓점을 공유하지 않는다. -/
  disjoint : ∀ a b (h : K.Adj a b) c d (h' : K.Adj c d), s(a, b) ≠ s(c, d) →
    Disjoint (walkInterior (path a b h)) (walkInterior (path c d h'))

namespace SubdivisionPaths

variable {K : SimpleGraph W} {G : SimpleGraph V}

/-- `K`에서 인접한 두 꼭짓점의 분기점은 서로 다르다. -/
theorem branch_ne (P : SubdivisionPaths K G) {a b : W} (h : K.Adj a b) :
    P.branch a ≠ P.branch b :=
  P.branch.injective.ne h.ne

/-- 반대 방향 경로의 내부는 같다. -/
theorem walkInterior_path_symm (P : SubdivisionPaths K G) {a b : W} (h : K.Adj a b) :
    walkInterior (P.path b a h.symm) = walkInterior (P.path a b h) := by
  rw [P.path_symm, walkInterior_reverse]

/-- 세분하지 않은 경우: `K.map f ≤ G`이면 `K`의 각 변을 `G`의 한 변짜리 경로로 하는 경로 체계가 있다.
`G`에 다른 변이 더 있어도 된다. -/
def ofMapLE (f : W ↪ V) (hle : K.map f ≤ G) : SubdivisionPaths K G where
  branch := f
  path a b h := Walk.cons (hle (map_adj_apply.2 h)) Walk.nil
  isPath a b h := by
    rw [Walk.cons_isPath_iff]
    exact ⟨Walk.IsPath.nil, by simpa using f.injective.ne h.ne⟩
  path_symm _ _ _ := rfl
  interior_not_branch a b h x hx := by simp at hx
  disjoint a b h c d h' _ := by simp

@[simp] theorem ofMapLE_branch (f : W ↪ V) (hle : K.map f ≤ G) : (ofMapLE f hle).branch = f := rfl

end SubdivisionPaths

end Kuratowski
