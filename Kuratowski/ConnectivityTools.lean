import Kuratowski.ConnectedContraction

/-!
# Connectivity under deletion and minimal separating sets

Monotonicity of the connectivity bound, deletion of one vertex, the lower bound on the number of
neighbors, and a graph identity for deletion after contraction. In a `k`-connected graph each
vertex of a separating set of size `k` has a neighbor in every support component. This generalizes
the size-3 argument of `ConnectedContraction.lean` to arbitrary `k` without changing its
statements.
-/

namespace Kuratowski
open SimpleGraph
variable {V : Type*} [Finite V] {G : SimpleGraph V} {A : Set V} {j k : ℕ}

/-- Connectivity for fewer deletions follows from stronger connectivity. -/
theorem ConnectedOn.mono (h : ConnectedOn G k A) (hjk : j ≤ k) : ConnectedOn G j A := by
  refine ⟨by have := h.1; omega, fun S hS ↦ h.2 S (lt_of_lt_of_le hS hjk)⟩

/-- Deleting one vertex first lowers the connectivity bound by one. The base set is the original
set minus that vertex. -/
theorem ConnectedOn.deleteVertex (h : ConnectedOn G (k + 1) A) (v : V) :
    ConnectedOn (deleteVertices G {v}) k (A \ {v}) := by
  refine ⟨?_, ?_⟩
  · have hcard := h.1
    have hd := Set.ncard_le_ncard_sdiff_add_ncard A ({v} : Set V)
    rw [Set.ncard_singleton] at hd
    omega
  · intro S hS u hu w hw
    have hcard : (insert v S).ncard < k + 1 :=
      lt_of_le_of_lt (Set.ncard_insert_le v S) (by omega)
    have hu' : u ∈ A \ insert v S := ⟨hu.1.1, by
      rintro (rfl | huS)
      · exact hu.1.2 rfl
      · exact hu.2 huS⟩
    have hw' : w ∈ A \ insert v S := ⟨hw.1.1, by
      rintro (rfl | hwS)
      · exact hw.1.2 rfl
      · exact hw.2 hwS⟩
    apply (h.2 (insert v S) hcard u hu' w hw').mono
    intro a b hab
    refine ⟨⟨hab.1, fun ha ↦ hab.2.1 (Or.inl ha), fun hb ↦ hab.2.2 (Or.inl hb)⟩,
      fun ha ↦ hab.2.1 (Or.inr ha), fun hb ↦ hab.2.2 (Or.inr hb)⟩

/-- A vertex of a `k`-connected base set has at least `k` neighbors in the whole graph. -/
theorem ConnectedOn.ncard_neighborSet_ge (h : ConnectedOn G k A) {x : V} (hx : x ∈ A) :
    k ≤ (G.neighborSet x).ncard := by
  by_contra hle
  have hN : (G.neighborSet x).ncard < k := by omega
  have hi := Set.ncard_insert_le x (G.neighborSet x)
  have hc := h.1
  obtain ⟨z, hzA, hzx⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show (insert x (G.neighborSet x)).ncard < A.ncard by omega)
  have hr := h.2 (G.neighborSet x) hN x ⟨hx, fun hxx ↦ G.loopless.irrefl x hxx⟩ z
    ⟨hzA, fun hz ↦ hzx (Or.inr hz)⟩
  have hiso : (deleteVertices G (G.neighborSet x)).IsIsolated x :=
    fun _ hab ↦ hab.2.2 hab.1
  have heq := eq_of_isIsolated_of_reachable hiso hr
  exact hzx (Or.inl heq)

omit [Finite V] in
/-- Deleting the kept vertex after contraction gives the graph with both original ends
deleted. -/
theorem deleteVertices_contractEdge_left {x y : V} :
    deleteVertices (contractEdge G x y) {x} = deleteVertices G {x, y} := by
  ext a b
  simp only [deleteVertices_adj, contractEdge_adj, Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨⟨_, hay, hby, hab | ⟨rfl, _⟩ | ⟨rfl, _⟩⟩, hax, hbx⟩
    · exact ⟨hab, fun h ↦ h.elim hax hay, fun h ↦ h.elim hbx hby⟩
    · exact False.elim (hax rfl)
    · exact False.elim (hbx rfl)
  · rintro ⟨hab, ha, hb⟩
    exact ⟨⟨hab.ne, fun h ↦ ha (Or.inr h), fun h ↦ hb (Or.inr h), Or.inl hab⟩,
      fun h ↦ ha (Or.inl h), fun h ↦ hb (Or.inl h)⟩

/-- In a `k`-connected graph, each vertex of a separating set of size `k` has a neighbor in
every support component. -/
theorem exists_adj_mem_sepComponent_of_connectedOn (hG : ConnectedOn G k G.support)
    {T : Set V} (hT : T.ncard = k)
    (hsep : Separates G T) {c : V} (hc : c ∈ G.support \ T) {t : V} (ht : t ∈ T) :
    ∃ d ∈ sepComponent G T c, G.Adj t d := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  -- a vertex `e` outside `C`
  have hout : ∃ e ∈ G.support \ T, e ∉ sepComponent G T c := by
    obtain ⟨u, hu, v, hv, huv⟩ := hsep
    by_cases huC : u ∈ sepComponent G T c
    · refine ⟨v, hv, fun hvC ↦ huv ?_⟩
      exact huC.2.symm.trans hvC.2
    · exact ⟨u, hu, huC⟩
  obtain ⟨e, he, heC⟩ := hout
  -- deleting `T \ {t}` cannot leave `C`
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
  have hkpos : 0 < k := by
    rw [← hT]
    exact (Set.ncard_pos (Set.toFinite _)).2 ⟨t, ht⟩
  have hT' : (T \ {t}).ncard < k := by
    rw [Set.ncard_sdiff_singleton_of_mem ht, hT]
    omega
  obtain ⟨p⟩ := hG.2 (T \ {t}) hT' c ⟨hc.1, fun h ↦ hc.2 h.1⟩ e ⟨he.1, fun h ↦ he.2 h.1⟩
  exact heC (stay p ⟨hc, .refl _⟩)


end Kuratowski
