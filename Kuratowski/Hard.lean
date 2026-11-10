import Kuratowski.RotationOrder
import Kuratowski.AlternatingNeighbors
import Kuratowski.CommonNeighbors
import Kuratowski.Contractible
import Kuratowski.NeighborWord
import Kuratowski.Reduction
import Kuratowski.Subdivision

/-!
# Kuratowski's theorem

A finite graph is planar iff it contains no subdivision of `K₅` or `K₃,₃`.
Planarity here means the existence of a rotation system with Euler characteristic
`2 * |ConnectedComponent|`; the topological embedding correspondence is not formalized.

The hard direction is strong induction on the number of edges. `Reduction`
reduces to a 3-connected graph; `Small` handles at most four non-isolated vertices.
Contract a 3-connectivity-preserving edge `xy` and apply the induction hypothesis.
Classify the inverse-rotation word of `x`'s neighbors in the contracted graph:
* the interval case reconstructs a planar rotation system;
* three common neighbors give a `K₅` subdivision;
* alternating neighbors give a `K₃,₃` subdivision.

The latter two cases contradict `KuratowskiFree`. The easy direction is
`IsPlanar.not_containsSubdivision`. Blueprint: `thm:hard`, `thm:kuratowski`.
-/

namespace Kuratowski

open SimpleGraph Equiv Equiv.Perm Function

variable {V : Type*}

/-- A set of size at least three contains two distinct elements avoiding a prescribed point. -/
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

section Main

variable {G : SimpleGraph V} {x y : V}

/-- A Kuratowski-free 3-connected graph is planar if contracting an edge preserves
3-connectivity and the contracted graph has a genus-zero rotation system. -/
theorem isPlanar_of_contractible [Finite V] (hKF : KuratowskiFree G) (h3 : ThreeConnected G)
    (hxy : G.Adj x y) (h3' : ThreeConnected (contractEdge G x y))
    (R' : RotationSystem (contractEdge G x y))
    (hR' : R'.eulerChar = 2 * Nat.card (contractEdge G x y).ConnectedComponent) :
    IsPlanar G := by
  classical
  -- Each endpoint has at least three neighbors, hence two other than the opposite endpoint.
  have hdx := ConnectedOn.ncard_neighborSet_ge h3 (x := x) (G.mem_support.2 ⟨y, hxy⟩)
  have hdy := ConnectedOn.ncard_neighborSet_ge h3 (x := y) (G.mem_support.2 ⟨x, hxy.symm⟩)
  obtain ⟨a₁, ha₁, a₂, ha₂, ha₁₂, ha₁y, ha₂y⟩ := exists_two_mem_ne_of_three_le hdx y
  obtain ⟨b₁, hb₁, b₂, hb₂, hb₁₂, hb₁x, hb₂x⟩ := exists_two_mem_ne_of_three_le hdy x
  have hx' : ∀ z, G.Adj x z → z ≠ y → (contractEdge G x y).Adj x z := fun z hz hzy ↦
    ⟨hz.ne, hxy.ne, hzy, Or.inl hz⟩
  have hy' : ∀ z, G.Adj y z → z ≠ x → (contractEdge G x y).Adj x z := fun z hz hzx ↦
    ⟨fun h ↦ hzx h.symm, hxy.ne, hz.ne', Or.inr (Or.inl ⟨rfl, hz⟩)⟩
  -- `x` has at least three neighbors in `G/xy`.
  have hN := ConnectedOn.ncard_neighborSet_ge h3' (x := x)
    ((contractEdge G x y).mem_support.2 ⟨a₁, hx' a₁ ha₁ ha₁y⟩)
  have : NeZero ((contractEdge G x y).neighborSet x).ncard := ⟨by omega⟩
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : (contractEdge G x y).Dart, d₀.fst = x :=
    ⟨⟨(x, a₁), hx' a₁ ha₁ ha₁y⟩, rfl⟩
  -- J2 gives a cycle in `G/xy - x = G - {x, y}`, with neighbor `u_j` at position `p j`.
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
  -- The word has at least two `X/B` positions and at least two `Y/B` positions.
  have hX : 2 ≤ (CyclicWord.xPositions (R'.neighborWord d₀)).card :=
    R'.two_le_card_of_two_adj d₀ hd₀ _ (G.Adj x) (fun _ ↦ R'.mem_xPositions_neighborWord d₀)
      ha₁₂ (hx' a₁ ha₁ ha₁y) (hx' a₂ ha₂ ha₂y) ha₁ ha₂
  have hY : 2 ≤ (CyclicWord.yPositions (R'.neighborWord d₀)).card :=
    R'.two_le_card_of_two_adj d₀ hd₀ _ (G.Adj y) (fun _ ↦ R'.mem_yPositions_neighborWord d₀)
      hb₁₂ (hy' b₁ hb₁ hb₁x) (hy' b₂ hb₂ hb₂x) hb₁ hb₂
  rcases CyclicWord.classify (R'.neighborWord d₀) hX hY with hc | hB | halt
  · -- (a) Clustered neighbors: split the contracted vertex.
    exact IsPlanar.of_contractEdge_of_interval hxy R' hR'
      (R'.intervalWord_of_clustered d₀ hd₀ hc)
  · -- (b) Three common neighbors: a `K₅` subdivision.
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
  · -- (c) Alternating neighbors: a `K₃,₃` subdivision.
    exfalso
    apply hKF.2
    obtain ⟨u, hu, w, hw, ⟨a, ha, hua⟩, b, hb, hwb⟩ := halt
    exact containsSubdivision_K33_of_alternating (C.mono hle) hxy hxC hyC
      (CyclicWord.sbtw_cast_positions p hpm hinc hua)
      (CyclicWord.sbtw_cast_positions p hpm hinc hwb)
      (hYC u hu) (hYC w hw) (hXC a ha) (hXC b hb)

/-- Induction step: if every Kuratowski-free graph with fewer edges is planar, so is `G`. -/
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

/-- Kuratowski's theorem, hard direction: a finite graph with no subdivision of
`K₅` or `K₃,₃` is planar (blueprint `thm:hard`). -/
theorem isPlanar_of_kuratowskiFree [Finite V] (h5 : ¬ ContainsSubdivision G K5)
    (h33 : ¬ ContainsSubdivision G K33) : IsPlanar G := by
  suffices key : ∀ n (H : SimpleGraph V), H.edgeSet.ncard = n → KuratowskiFree H → IsPlanar H from
    key _ G rfl ⟨h5, h33⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hn hKF
    exact isPlanar_of_kuratowskiFree_of_lt hKF fun K hK hlt ↦ ih _ (by omega) K rfl hK

/-- Kuratowski's theorem: a finite graph is planar iff it contains no subdivision
of `K₅` or `K₃,₃` (blueprint `thm:kuratowski`). -/
theorem isPlanar_iff_kuratowskiFree [Finite V] :
    IsPlanar G ↔ ¬ ContainsSubdivision G K5 ∧ ¬ ContainsSubdivision G K33 := by
  classical
  exact ⟨IsPlanar.not_containsSubdivision, fun h ↦ isPlanar_of_kuratowskiFree h.1 h.2⟩

end Main

end Kuratowski
