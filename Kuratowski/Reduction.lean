import Kuratowski.ConnectivityTools
import Kuratowski.PathReplacement
import Kuratowski.GlueEdge
import Kuratowski.Small

/-!
# A non-planar KF graph with the fewest edges is 3-connected

Blueprint `thm:reduce`. Assume that every KF graph on the same finite vertex type with fewer edges
is planar. Then the original graph is planar or 3-connected (`isPlanar_or_threeConnected`).

Split the graph into the side keeping one support component together with the separating set, and
the opposite side with that component deleted. For separating sets of size 0 or 1, both sides are
planar by the induction hypothesis, and a disjoint union or a one-vertex gluing finishes. For a
separating set of size 2, add the shared edge to both sides. A path through the opposite component
shows that the added edge keeps the side KF, and each side misses at least two original edges
while adding one, so the number of edges strictly decreases. The last step is gluing along a common
edge.
-/

namespace Kuratowski
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- If the size condition holds but the graph is not `k`-connected, there is a small separating
set inside the support. -/
theorem exists_separates_of_not_connectedOn [Finite V] {k : ℕ} (hcard : k + 1 ≤ G.support.ncard)
    (hnot : ¬ ConnectedOn G k G.support) :
    ∃ T ⊆ G.support, T.ncard < k ∧ Separates G T := by
  classical
  by_contra hno
  apply hnot
  refine ⟨hcard, ?_⟩
  intro S hS u hu v hv
  by_contra huv
  apply hno
  refine ⟨S ∩ G.support, Set.inter_subset_right, ?_, u, ?_, v, ?_, ?_⟩
  · exact lt_of_le_of_lt (Set.ncard_le_ncard Set.inter_subset_left) hS
  · exact ⟨hu.1, fun h ↦ hu.2 h.1⟩
  · exact ⟨hv.1, fun h ↦ hv.2 h.1⟩
  · simpa only [deleteVertices_inter_support] using huv

/-- An edge leaving a support component to a vertex outside the deleted set ends in the same
component. -/
theorem mem_sepComponent_of_adj {T : Set V} {c a b : V} (ha : a ∈ sepComponent G T c)
    (hab : G.Adj a b) (hb : b ∉ T) : b ∈ sepComponent G T c :=
  ⟨⟨hab.mem_support_right, hb⟩, ha.2.trans (Adj.reachable ⟨hab, ha.1.2, hb⟩)⟩

/-- The side keeping one support component and the separating set. -/
def separationLeft (G : SimpleGraph V) (T : Set V) (c : V) : SimpleGraph V :=
  deleteVertices G (sepComponent G T c ∪ T)ᶜ

/-- The opposite side, with only that support component deleted. -/
def separationRight (G : SimpleGraph V) (T : Set V) (c : V) : SimpleGraph V :=
  deleteVertices G (sepComponent G T c)

lemma separationLeft_le (T : Set V) (c : V) : separationLeft G T c ≤ G := deleteVertices_le _ _
lemma separationRight_le (T : Set V) (c : V) : separationRight G T c ≤ G := deleteVertices_le _ _

/-- The two sides cover the original graph. -/
theorem separation_sup (T : Set V) (c : V) : separationLeft G T c ⊔ separationRight G T c = G := by
  classical
  refine le_antisymm (sup_le (separationLeft_le T c) (separationRight_le T c)) ?_
  have next : ∀ a b, G.Adj a b → a ∈ sepComponent G T c → b ∈ sepComponent G T c ∪ T := by
    intro a b hab ha
    by_cases hb : b ∈ T
    · exact Or.inr hb
    · exact Or.inl (mem_sepComponent_of_adj ha hab hb)
  intro a b hab
  by_cases ha : a ∈ sepComponent G T c
  · exact Or.inl ⟨hab, not_not.mpr (Or.inl ha), not_not.mpr (next a b hab ha)⟩
  by_cases hb : b ∈ sepComponent G T c
  · exact Or.inl ⟨hab, not_not.mpr (next b a hab.symm hb), not_not.mpr (Or.inl hb)⟩
  exact Or.inr ⟨hab, ha, hb⟩

/-- The supports of the two sides intersect inside the separating set. -/
theorem separation_support_inter_subset (T : Set V) (c : V) :
    (separationLeft G T c).support ∩ (separationRight G T c).support ⊆ T := by
  classical
  intro a ha
  obtain ⟨b, hab⟩ := (mem_support _).1 ha.1
  obtain ⟨d, had⟩ := (mem_support _).1 ha.2
  have hamem : a ∈ sepComponent G T c ∪ T := not_not.mp hab.2.1
  exact hamem.resolve_left had.2.1

/-- A subgraph missing at least one original edge has fewer edges. -/
theorem ncard_edgeSet_lt_of_not_adj [Finite V] {H : SimpleGraph V} (hHG : H ≤ G) {a b : V}
    (hab : G.Adj a b) (hnot : ¬ H.Adj a b) : H.edgeSet.ncard < G.edgeSet.ncard := by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  refine ⟨edgeSet_mono hHG, ?_⟩
  intro hback
  exact hnot (H.mem_edgeSet.mp (hback (G.mem_edgeSet.mpr hab)))

/-- Deleting a non-isolated vertex strictly decreases the number of edges. -/
theorem ncard_edgeSet_deleteVertices_lt [Finite V] {S : Set V} {a : V}
    (haS : a ∈ S) (ha : a ∈ G.support) :
    (deleteVertices G S).edgeSet.ncard < G.edgeSet.ncard := by
  obtain ⟨b, hab⟩ := (mem_support _).1 ha
  exact ncard_edgeSet_lt_of_not_adj (deleteVertices_le _ _) hab (fun h ↦ h.2.1 haS)

/-- The union of two planar graphs with a small intersection is planar. -/
theorem IsPlanar.sup_of_ncard_inter_le_one [Finite V] {H : SimpleGraph V}
    (hG : IsPlanar G) (hH : IsPlanar H)
    (hi : (G.support ∩ H.support).ncard ≤ 1) : IsPlanar (G ⊔ H) := by
  classical
  by_cases hempty : G.support ∩ H.support = ∅
  · exact hG.sup_of_disjoint hH (Set.disjoint_iff_inter_eq_empty.2 hempty)
  have hc : (G.support ∩ H.support).ncard = 1 := by
    have hp : 0 < (G.support ∩ H.support).ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 (Set.nonempty_iff_ne_empty.2 hempty)
    omega
  obtain ⟨v, hv⟩ := Set.ncard_eq_one.1 hc
  exact hG.sup_of_inter_eq_singleton hH hv

/-- A non-planar KF graph with the fewest edges is 2-connected. -/
theorem isPlanar_or_twoConnected [Finite V] (hKF : KuratowskiFree G)
    (hIH : ∀ H : SimpleGraph V, KuratowskiFree H → H.edgeSet.ncard < G.edgeSet.ncard → IsPlanar H) :
    IsPlanar G ∨ TwoConnected G := by
  classical
  by_cases hsmall : G.support.ncard ≤ 4
  · exact Or.inl (isPlanar_of_ncard_support_le_four G hsmall)
  by_cases h2 : TwoConnected G
  · exact Or.inr h2
  obtain ⟨T, hTG, hT, u, hu, v, hv, huv⟩ :=
    exists_separates_of_not_connectedOn (G := G) (k := 2) (by omega) h2
  have huC : u ∈ sepComponent G T u := ⟨hu, .refl _⟩
  have hvC : v ∉ sepComponent G T u := fun h ↦ huv h.2
  have hvout : v ∈ (sepComponent G T u ∪ T)ᶜ := by
    rintro (h | h)
    · exact hvC h
    · exact hv.2 h
  have hleft : (separationLeft G T u).edgeSet.ncard < G.edgeSet.ncard :=
    ncard_edgeSet_deleteVertices_lt hvout hv.1
  have hright : (separationRight G T u).edgeSet.ncard < G.edgeSet.ncard :=
    ncard_edgeSet_deleteVertices_lt huC hu.1
  have hPL := hIH _ (hKF.mono (separationLeft_le T u)) hleft
  have hPR := hIH _ (hKF.mono (separationRight_le T u)) hright
  have hbound := Set.ncard_le_ncard (separation_support_inter_subset (G := G) T u)
  have hP := hPL.sup_of_ncard_inter_le_one hPR (by omega)
  rw [separation_sup] at hP
  exact Or.inl hP


/-- A path between the two separator vertices through one component of a 2-separation. -/
theorem exists_path_in_sepComponent [Finite V] (h2 : TwoConnected G) {x y c : V}
    (hxy : x ≠ y) (hsep : Separates G {x, y}) (hc : c ∈ G.support \ {x, y}) :
    ∃ p : G.Walk x y, p.IsPath ∧ ∀ w ∈ walkInterior p, w ∈ sepComponent G {x, y} c := by
  classical
  have hT : ({x, y} : Set V).ncard = 2 := Set.ncard_pair hxy
  obtain ⟨a, ha, hxa⟩ := exists_adj_mem_sepComponent_of_connectedOn h2 hT hsep hc
    (t := x) (by simp)
  obtain ⟨b, hb, hyb⟩ := exists_adj_mem_sepComponent_of_connectedOn h2 hT hsep hc
    (t := y) (by simp)
  obtain ⟨q⟩ := ha.2.symm.trans hb.2
  have stay : ∀ {u v : V} (p : (deleteVertices G {x, y}).Walk u v),
      u ∈ sepComponent G {x, y} c → ∀ w ∈ p.support, w ∈ sepComponent G {x, y} c := by
    intro u v p
    induction p with
    | @nil u =>
      intro hu w hw
      have he : w = u := by simpa only [Walk.support_nil, List.mem_singleton] using hw
      exact he.symm ▸ hu
    | @cons u z v huz p ih =>
      intro hu w hw
      rw [Walk.support_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact hu
      · exact ih (mem_sepComponent_of_adj hu huz.1 huz.2.2) w hw
  let p₀ : G.Walk x y := .cons hxa ((q.mapLe (deleteVertices_le _ _)).append hyb.symm.toWalk)
  refine ⟨p₀.bypass, p₀.bypass_isPath, ?_⟩
  intro w hw
  have hmem := p₀.support_bypass_subset_support hw.1
  simp only [p₀, Walk.support_cons, List.mem_cons, Walk.mem_support_append_iff,
    Walk.support_mapLe_eq_support, Walk.support_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with h | h | rfl | h
  · exact False.elim (hw.2.1 h)
  · exact stay q ha w h
  · exact hb
  · exact False.elim (hw.2.2 h)

/-- Adding one edge to a subgraph that misses two edges still gives fewer edges than the
original. -/
theorem ncard_sup_edge_lt_of_two_missing [Finite V] {H : SimpleGraph V} (hle : H ≤ G)
    {e f : Sym2 V} (he : e ∈ G.edgeSet) (hf : f ∈ G.edgeSet) (hne : e ≠ f)
    (heH : e ∉ H.edgeSet) (hfH : f ∉ H.edgeSet) (x y : V) :
    (H ⊔ edge x y).edgeSet.ncard < G.edgeSet.ncard := by
  have hsub : H.edgeSet ⊆ G.edgeSet \ {e, f} := by
    intro a ha
    refine ⟨edgeSet_mono hle ha, ?_⟩
    rintro (rfl | rfl)
    · exact heH ha
    · exact hfH ha
  have hcard := Set.ncard_sdiff_add_ncard_of_subset
    (show ({e, f} : Set (Sym2 V)) ⊆ G.edgeSet by
      intro a ha; rcases ha with rfl | rfl; exact he; exact hf)
  rw [Set.ncard_pair hne] at hcard
  have hlecard := Set.ncard_le_ncard hsub
  have hmore : (H ⊔ edge x y).edgeSet.ncard ≤ H.edgeSet.ncard + 1 := by
    calc (H ⊔ edge x y).edgeSet.ncard ≤ (insert s(x, y) H.edgeSet).ncard := by
          refine Set.ncard_le_ncard ?_ (Set.toFinite _)
          rw [edgeSet_sup]
          exact Set.union_subset (fun _ ha ↦ Or.inr ha)
            (fun _ ha ↦ Or.inl (edgeSet_edge_subset ha))
      _ ≤ H.edgeSet.ncard + 1 := Set.ncard_insert_le _ _
  omega

/-- Show that the added edge keeps the side KF using a path through the opposite component, and
apply the induction hypothesis. -/
theorem isPlanar_augmented_of_isolated_component [Finite V] (h2 : TwoConnected G)
    (hKF : KuratowskiFree G)
    (hIH : ∀ H : SimpleGraph V, KuratowskiFree H → H.edgeSet.ncard < G.edgeSet.ncard → IsPlanar H)
    {x y c : V} (hxy : x ≠ y) (hsep : Separates G {x, y}) (hc : c ∈ G.support \ {x, y})
    {H : SimpleGraph V} (hle : H ≤ G) (hiso : ∀ w ∈ sepComponent G {x, y} c, H.IsIsolated w) :
    IsPlanar (H ⊔ edge x y) := by
  obtain ⟨p, hp, hint⟩ := exists_path_in_sepComponent h2 hxy hsep hc
  have hKH : KuratowskiFree (H ⊔ edge x y) :=
    hKF.sup_edge_of_path hle hxy p hp (fun w hw ↦ hiso w (hint w hw))
  have hT : ({x, y} : Set V).ncard = 2 := Set.ncard_pair hxy
  obtain ⟨a, ha, hxa⟩ := exists_adj_mem_sepComponent_of_connectedOn h2 hT hsep hc
    (t := x) (by simp)
  obtain ⟨b, hb, hyb⟩ := exists_adj_mem_sepComponent_of_connectedOn h2 hT hsep hc
    (t := y) (by simp)
  have hne : s(x, a) ≠ s(y, b) := by
    rw [ne_eq, Sym2.eq_iff]
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact hxy h
    · exact hb.1.2 (Or.inl h.symm)
  exact hIH _ hKH (ncard_sup_edge_lt_of_two_missing hle hxa hyb hne
    (fun h ↦ hiso a ha x h.symm) (fun h ↦ hiso b hb y h.symm) x y)

/-- A non-planar KF graph with the fewest edges is 3-connected. -/
theorem isPlanar_or_threeConnected [Finite V] (hKF : KuratowskiFree G)
    (hIH : ∀ H : SimpleGraph V, KuratowskiFree H → H.edgeSet.ncard < G.edgeSet.ncard → IsPlanar H) :
    IsPlanar G ∨ ThreeConnected G := by
  classical
  by_cases hsmall : G.support.ncard ≤ 4
  · exact Or.inl (isPlanar_of_ncard_support_le_four G hsmall)
  obtain hP | h2 := isPlanar_or_twoConnected hKF hIH
  · exact Or.inl hP
  by_cases h3 : ThreeConnected G
  · exact Or.inr h3
  obtain ⟨T, hTG, hTlt, hsep⟩ :=
    exists_separates_of_not_connectedOn (G := G) (k := 3) (by omega) h3
  have hT : T.ncard = 2 := by
    obtain ⟨u, hu, v, hv, huv⟩ := hsep
    have hnot : ¬ T.ncard < 2 := fun h ↦ huv (h2.2 T h u hu v hv)
    omega
  obtain ⟨x, y, hxy, hTeq⟩ := Set.ncard_eq_two.1 hT
  subst T
  obtain ⟨u, hu, v, hv, huv⟩ := hsep
  have hsep : Separates G {x, y} := ⟨u, hu, v, hv, huv⟩
  have hdisj : ∀ w ∈ sepComponent G {x, y} v, w ∉ sepComponent G {x, y} u := by
    intro w hw hwu
    exact huv (hwu.2.trans hw.2.symm)
  have hleft := isPlanar_augmented_of_isolated_component h2 hKF hIH hxy hsep hv
    (separationLeft_le {x, y} u) (fun w hw ↦ isIsolated_deleteVertices _ (by
      rintro (hwC | hwT)
      · exact hdisj w hw hwC
      · exact hw.1.2 hwT))
  have hright := isPlanar_augmented_of_isolated_component h2 hKF hIH hxy hsep hu
    (separationRight_le {x, y} u) (fun w hw ↦ isIsolated_deleteVertices _ hw)
  have hs : (separationLeft G {x, y} u ⊔ edge x y).support ∩
      (separationRight G {x, y} u ⊔ edge x y).support = {x, y} := by
    ext w
    constructor
    · intro hw
      obtain ⟨a, ha | ha⟩ := (mem_support _).1 hw.1
      · obtain ⟨b, hb | hb⟩ := (mem_support _).1 hw.2
        · exact separation_support_inter_subset {x, y} u
            ⟨ha.mem_support_left, hb.mem_support_left⟩
        · rcases (edge_adj x y w b).1 hb with ⟨⟨rfl, _⟩ | ⟨rfl, _⟩, _⟩ <;> simp
      · rcases (edge_adj x y w a).1 ha with ⟨⟨rfl, _⟩ | ⟨rfl, _⟩, _⟩ <;> simp
    · intro hw
      rcases hw with hw | hw
      · rw [hw]
        exact ⟨(show (separationLeft G {x, y} u ⊔ edge x y).Adj x y from
          Or.inr ((edge_adj x y x y).2 ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩)).mem_support_left,
          (show (separationRight G {x, y} u ⊔ edge x y).Adj x y from
          Or.inr ((edge_adj x y x y).2 ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩)).mem_support_left⟩
      · rw [hw]
        exact ⟨(show (separationLeft G {x, y} u ⊔ edge x y).Adj y x from
          Or.inr ((edge_adj x y y x).2 ⟨Or.inr ⟨rfl, rfl⟩, hxy.symm⟩)).mem_support_left,
          (show (separationRight G {x, y} u ⊔ edge x y).Adj y x from
          Or.inr ((edge_adj x y y x).2 ⟨Or.inr ⟨rfl, rfl⟩, hxy.symm⟩)).mem_support_left⟩
  have hedge : (edge x y).Adj x y := (edge_adj x y x y).2 ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩
  have hP := hleft.sup_of_inter_eq_edge hright (Or.inr hedge) (Or.inr hedge) hs
  apply Or.inl
  apply hP.mono
  exact le_trans (le_of_eq (separation_sup (G := G) {x, y} u).symm)
    (sup_le_sup le_sup_left le_sup_left)

end Kuratowski

