import Kuratowski.SubdivisionOfPaths

/-!
# 경로 체계를 만드는 도구

* `walkInterior_copy`: 끝점 표기를 바꿔도 걸음의 내부는 같다.
* `SubdivisionPaths.containsSubdivision_of_finite`: `K`의 꼭짓점 타입 `W`가 유한하면 경로 체계에서 세분
  포함을 얻는다. `containsSubdivision_iff_paths`의 역방향은 `V`의 유한성을 가정하지만, 실제로는 처리할
  변 집합이 유한하면 충분하다. `K₅`, `K₃,₃`처럼 `W`가 유한할 때 `G` 쪽 가정 없이 쓴다.
* `SubdivisionPaths.ofLT`: `W`에 선형 순서가 있을 때 `a < b`인 변에만 경로를 주어 경로 체계를 만든다.
  반대 방향은 뒤집은 경로로 정의하므로 `path_symm`은 자동으로 성립한다.
-/

namespace Kuratowski

open SimpleGraph

variable {V W : Type*}

@[simp] theorem walkInterior_copy {G : SimpleGraph V} {u v u' v' : V} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') : walkInterior (p.copy hu hv) = walkInterior p := by
  subst hu hv
  rfl

namespace SubdivisionPaths

variable {K : SimpleGraph W} {G : SimpleGraph V}

theorem containsSubdivision_of_finite [Finite W] (P : SubdivisionPaths K G) :
    ContainsSubdivision G K := by
  obtain ⟨H, hS, hle⟩ := P.exists_isSubdivision_le_of_finite
  exact ⟨P.branch, H, hS, hle⟩

section OfLT

variable [LinearOrder W] (f : W ↪ V) (p : ∀ a b, a < b → K.Adj a b → G.Walk (f a) (f b))

/-- `ofLT`의 경로: `a < b`이면 주어진 경로, 아니면 반대 방향 경로를 뒤집은 것. -/
def ofLTPath (a b : W) (h : K.Adj a b) : G.Walk (f a) (f b) :=
  if hab : a < b then p a b hab h
  else (p b a (lt_of_le_of_ne (not_lt.1 hab) h.ne.symm) h.symm).reverse

theorem exists_ofLTPath (a b : W) (h : K.Adj a b) :
    ∃ a' b', ∃ (hab : a' < b') (h₀ : K.Adj a' b'), s(a', b') = s(a, b) ∧
      walkInterior (ofLTPath f p a b h) = walkInterior (p a' b' hab h₀) ∧
      ((ofLTPath f p a b h).IsPath ↔ (p a' b' hab h₀).IsPath) := by
  by_cases hab : a < b
  · exact ⟨a, b, hab, h, rfl, by simp only [ofLTPath, hab, ↓reduceDIte],
      by simp only [ofLTPath, hab, ↓reduceDIte]⟩
  · have hba := lt_of_le_of_ne (not_lt.1 hab) h.ne.symm
    exact ⟨b, a, hba, h.symm, Sym2.eq_swap,
      by simp only [ofLTPath, hab, ↓reduceDIte, walkInterior_reverse],
      by simp only [ofLTPath, hab, ↓reduceDIte, Walk.isPath_reverse_iff]⟩

/-- `a < b`인 변에만 경로를 주어 경로 체계를 만든다. 반대 방향은 뒤집은 경로다. -/
def ofLT (hp : ∀ a b (hab : a < b) (h : K.Adj a b), (p a b hab h).IsPath)
    (hint : ∀ a b (hab : a < b) (h : K.Adj a b),
      ∀ z ∈ walkInterior (p a b hab h), z ∉ Set.range f)
    (hdisj : ∀ a b (hab : a < b) (h : K.Adj a b) c d (hcd : c < d) (h' : K.Adj c d),
      s(a, b) ≠ s(c, d) → Disjoint (walkInterior (p a b hab h)) (walkInterior (p c d hcd h'))) :
    SubdivisionPaths K G where
  branch := f
  path := ofLTPath f p
  isPath a b h := by
    obtain ⟨a', b', hab, h₀, -, -, hiff⟩ := exists_ofLTPath f p a b h
    exact hiff.2 (hp a' b' hab h₀)
  path_symm a b h := by
    by_cases hab : a < b
    · simp only [ofLTPath, not_lt.2 hab.le, hab, ↓reduceDIte]
    · have hba : b < a := lt_of_le_of_ne (not_lt.1 hab) h.ne.symm
      simp only [ofLTPath, hba, hab, ↓reduceDIte, Walk.reverse_reverse]
  interior_not_branch a b h z hz := by
    obtain ⟨a', b', hab, h₀, -, hi, -⟩ := exists_ofLTPath f p a b h
    rw [hi] at hz
    exact hint a' b' hab h₀ z hz
  disjoint a b h c d h' hne := by
    obtain ⟨a', b', hab, h₀, e1, i1, -⟩ := exists_ofLTPath f p a b h
    obtain ⟨c', d', hcd, h₁, e2, i2, -⟩ := exists_ofLTPath f p c d h'
    rw [i1, i2]
    exact hdisj a' b' hab h₀ c' d' hcd h₁ (by rw [e1, e2]; exact hne)

@[simp] theorem ofLT_branch (hp) (hint) (hdisj) : (ofLT f p hp hint hdisj).branch = f := rfl

end OfLT

end SubdivisionPaths

end Kuratowski
