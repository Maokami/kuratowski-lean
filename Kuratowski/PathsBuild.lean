import Kuratowski.SubdivisionOfPaths

/-!
# Tools for building path systems

* `walkInterior_copy`: changing the endpoint notation does not change the interior of a walk.
* `SubdivisionPaths.containsSubdivision_of_finite`: if the vertex type `W` of `K` is finite, a path
  system gives a contained subdivision. The reverse direction of `containsSubdivision_iff_paths`
  assumes `V` finite, but it suffices that the set of edges to process is finite. We use this for
  finite `W` such as `K₅` and `K₃,₃`, with no assumption on `G`.
* `SubdivisionPaths.ofLT`: for a linear order on `W`, build a path system from paths given only for
  edges with `a < b`. The opposite direction is the reversed path, so `path_symm` holds
  automatically.
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

/-- The path of `ofLT`: the given path if `a < b`, otherwise the reverse of the path in the
opposite direction. -/
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

/-- Build a path system from paths given only for edges with `a < b`. The opposite direction is
the reversed path. -/
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
