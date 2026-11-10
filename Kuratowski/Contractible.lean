import Kuratowski.ConnectedContraction

/-!
# Contractible edges (blueprint `thm:contractible`)

A 3-connected graph whose support has at least 5 vertices has an edge whose contraction is still
3-connected (`ThreeConnected.exists_contractible`). We follow the proof of Diestel, *Graph
Theory*, 6th ed., Lemma 3.2.4 (5th ed., 3.2.1). The support condition replaces `G ≠ K₄` and is used
only to show that the contraction has at least 4 support vertices.

Suppose no edge is contractible. Then for each edge `xy` there is `z` such that `{x, y, z}`
separates `G`. Choose such `(x, y, z)` and a component `C` of `G - {x, y, z}` with `|C|` minimal.
`z` has a neighbor `v` in `C`, and the edge `zv` also has a separating set `{z, v, w}`. Since
`x ∼ y`, `G - {z, v, w}` has a component `D` avoiding `x` and `y`. The neighbors of `v` in `D` lie
in `C`, so `D ⊆ C`; since `v ∈ C \ D`, `|D| < |C|`, a contradiction.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Finite V]

/-- Blueprint `thm:contractible` (Diestel, 6th ed., Lemma 3.2.4): a 3-connected graph whose
support has at least 5 vertices has an edge whose contraction is still 3-connected. -/
theorem ThreeConnected.exists_contractible (hG : ThreeConnected G) (h5 : 5 ≤ G.support.ncard) :
    ∃ x y, G.Adj x y ∧ ThreeConnected (contractEdge G x y) := by
  classical
  by_contra hno
  simp only [not_exists, not_and] at hno
  -- a separating set `{x, y, z}` and a representative `c` of the component
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
  -- a neighbor `v` of `z` in `C`, and the separating set `{z, v, w}` of the edge `zv`
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
  -- the vertices among `x`, `y` outside `T'` are connected to each other
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
  -- a component `D` not reachable from `r` avoids `x` and `y`
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
  -- walks from `D` stay in `D` and avoid `T`
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
  -- a neighbor `d` of `v` in `D` lies in `C`
  obtain ⟨d, hdD, hvd⟩ :=
    exists_adj_mem_sepComponent hG hT'3 hsep' hd₀ (t := v) ((hmem' v).2 (Or.inr (Or.inl rfl)))
  have hdC : d ∈ C := ⟨⟨hdD.1.1, hnotT d hdD⟩, hvC.2.trans (Adj.reachable ⟨hvd, hvC.1.2,
    hnotT d hdD⟩)⟩
  have hDC : D ⊆ C := by
    intro a ha
    obtain ⟨p⟩ := (hdD.2.symm.trans ha.2 : (deleteVertices G T').Reachable d a)
    obtain ⟨hda, -⟩ := stay p hdD
    exact ⟨⟨ha.1.1, hnotT a ha⟩, hdC.2.trans hda⟩
  -- `v ∈ C \ D`, so `D` is smaller, contradicting minimality
  have hvD : v ∉ D := fun h ↦ h.1.2 ((hmem' v).2 (Or.inr (Or.inl rfl)))
  have hlt : D.ncard < C.ncard := Set.ncard_lt_ncard ⟨hDC, fun h ↦ hvD (h hvC)⟩
  have hle : Nat.find hex ≤ D.ncard := hmin z v w d₀ ⟨hzv, hw, hwz, hwv, hsep', hd₀⟩
  omega

end Kuratowski
