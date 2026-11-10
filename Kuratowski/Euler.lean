import Kuratowski.Deletion
import Kuratowski.Components

/-!
# Euler's inequality and subgraphs

* **Euler's inequality** (`RotationSystem.eulerChar_le`): every rotation system satisfies
  `V - E + F ≤ 2 · (number of connected components)`. The proof is by induction on the number of
  edges. When an edge `uv` is deleted:
  - if the two darts of `uv` lie on the same face, `F` increases by 1, so the Euler characteristic
    increases by 2, and the number of components increases by at most one;
  - if they lie on different faces, `F` decreases by 1, so the Euler characteristic is unchanged,
    and `uv` is not a bridge, so the number of components is unchanged.
* **Subgraphs** (`IsPlanar.mono`): a subgraph of a planar graph is planar. The same computation
  together with Euler's inequality shows that deleting one edge preserves planarity; iterate.
-/

namespace Kuratowski

open Equiv Equiv.Perm SimpleGraph

variable {V : Type*} [Finite V] [DecidableEq V]

namespace RotationSystem

omit [Finite V] [DecidableEq V] in
/-- For a graph without edges, `V - E + F = 2V = 2c`. -/
lemma eulerChar_of_edgeSet_eq_empty {G : SimpleGraph V} (R : RotationSystem G)
    (h : G.edgeSet = ∅) : R.eulerChar = 2 * Nat.card G.ConnectedComponent := by
  have hD : IsEmpty G.Dart := ⟨fun d => by
    have := d.edge_mem
    rw [h] at this
    exact this⟩
  have hF : orbitCount R.facePerm = 0 := by
    have : IsEmpty R.Face := ⟨fun q => Quotient.inductionOn q fun x => hD.elim x⟩
    exact Nat.card_of_isEmpty
  have hI : {v | G.IsIsolated v}.ncard = Nat.card V := by
    have : {v | G.IsIsolated v} = Set.univ := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro w hw
      have : s(v, w) ∈ G.edgeSet := hw
      rw [h] at this
      exact this
    rw [this, Set.ncard_univ]
  have hc := card_connectedComponent_of_edgeSet_eq_empty G h
  unfold eulerChar numFaces
  rw [h, hF, hI, hc, Set.ncard_empty]
  push_cast
  ring

/-- Euler characteristic after deleting an edge `uv`: it increases by 2 if the two darts lie on
the same face. -/
lemma eulerChar_del_of_sameCycle {G : SimpleGraph V} (R : RotationSystem G) (d : G.Dart)
    (h : SameCycle R.facePerm d d.symm) : (R.del d).eulerChar = R.eulerChar + 2 := by
  have hE : (G.deleteEdges {d.edge}).edgeSet.ncard + 1 = G.edgeSet.ncard :=
    ncard_edgeSet_deleteEdges G d.adj
  have := R.numFaces_del_of_sameCycle d h
  unfold eulerChar
  rw [this]
  push_cast
  omega

/-- Euler characteristic after deleting an edge `uv`: it is unchanged if the two darts lie on
different faces. -/
lemma eulerChar_del_of_not_sameCycle {G : SimpleGraph V} (R : RotationSystem G) (d : G.Dart)
    (h : ¬ SameCycle R.facePerm d d.symm) : (R.del d).eulerChar = R.eulerChar := by
  have hE : (G.deleteEdges {d.edge}).edgeSet.ncard + 1 = G.edgeSet.ncard :=
    ncard_edgeSet_deleteEdges G d.adj
  have := R.numFaces_del_of_not_sameCycle d h
  unfold eulerChar
  omega

lemma eulerChar_le_aux (n : ℕ) :
    ∀ {G : SimpleGraph V} (R : RotationSystem G), G.edgeSet.ncard = n →
      R.eulerChar ≤ 2 * Nat.card G.ConnectedComponent := by
  induction n with
  | zero =>
    intro G R hn
    have h : G.edgeSet = ∅ := (Set.ncard_eq_zero (s := G.edgeSet)).1 hn
    exact (R.eulerChar_of_edgeSet_eq_empty h).le
  | succ n ih =>
    intro G R hn
    obtain ⟨e, he⟩ : G.edgeSet.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    induction e using Sym2.ind with | h u v => ?_
    have hadj : G.Adj u v := he
    set d : G.Dart := ⟨(u, v), hadj⟩
    have hE : (G.deleteEdges {d.edge}).edgeSet.ncard + 1 = G.edgeSet.ncard :=
      ncard_edgeSet_deleteEdges G hadj
    have ih' := ih (R.del d) (by omega)
    by_cases h : SameCycle R.facePerm d d.symm
    · have hχ := R.eulerChar_del_of_sameCycle d h
      have hc : Nat.card (G.deleteEdges {d.edge}).ConnectedComponent ≤
          Nat.card G.ConnectedComponent + 1 := card_connectedComponent_deleteEdges_le G u v
      omega
    · have hχ := R.eulerChar_del_of_not_sameCycle d h
      have hc : Nat.card (G.deleteEdges {d.edge}).ConnectedComponent =
          Nat.card G.ConnectedComponent :=
        card_connectedComponent_deleteEdges_eq G (R.reachable_del_of_not_sameCycle d h)
      rw [hc] at ih'
      omega

/-- **Euler's inequality**: every rotation system satisfies
`V - E + F ≤ 2 · (number of connected components)`. -/
theorem eulerChar_le {G : SimpleGraph V} (R : RotationSystem G) :
    R.eulerChar ≤ 2 * Nat.card G.ConnectedComponent :=
  eulerChar_le_aux _ R rfl

end RotationSystem

/-- Deleting one edge of a planar graph gives a planar graph. -/
theorem IsPlanar.deleteEdge {G : SimpleGraph V} (hG : IsPlanar G) {u v : V} (huv : G.Adj u v) :
    IsPlanar (G.deleteEdges {s(u, v)}) := by
  obtain ⟨R, hR⟩ := hG
  set d : G.Dart := ⟨(u, v), huv⟩
  refine ⟨R.del d, le_antisymm (R.del d).eulerChar_le ?_⟩
  by_cases h : SameCycle R.facePerm d d.symm
  · have hχ := R.eulerChar_del_of_sameCycle d h
    have hc : Nat.card (G.deleteEdges {d.edge}).ConnectedComponent ≤
        Nat.card G.ConnectedComponent + 1 := card_connectedComponent_deleteEdges_le G u v
    change 2 * (Nat.card (G.deleteEdges {d.edge}).ConnectedComponent : ℤ) ≤ (R.del d).eulerChar
    omega
  · have hχ := R.eulerChar_del_of_not_sameCycle d h
    have hc : Nat.card (G.deleteEdges {d.edge}).ConnectedComponent =
        Nat.card G.ConnectedComponent :=
      card_connectedComponent_deleteEdges_eq G (R.reachable_del_of_not_sameCycle d h)
    change 2 * (Nat.card (G.deleteEdges {d.edge}).ConnectedComponent : ℤ) ≤ (R.del d).eulerChar
    rw [hc]
    omega

lemma IsPlanar.mono_aux (n : ℕ) :
    ∀ {G H : SimpleGraph V}, IsPlanar G → H ≤ G → (G.edgeSet \ H.edgeSet).ncard = n →
      IsPlanar H := by
  induction n with
  | zero =>
    intro G H hG hHG hn
    have h : G.edgeSet \ H.edgeSet = ∅ := (Set.ncard_eq_zero (s := G.edgeSet \ H.edgeSet)).1 hn
    have : G = H := by
      apply le_antisymm _ hHG
      rw [← edgeSet_subset_edgeSet]
      exact Set.sdiff_eq_empty.1 h
    exact this ▸ hG
  | succ n ih =>
    intro G H hG hHG hn
    obtain ⟨e, he⟩ : (G.edgeSet \ H.edgeSet).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    induction e using Sym2.ind with | h u v => ?_
    have huv : G.Adj u v := he.1
    refine ih (hG.deleteEdge huv) ?_ ?_
    · intro p q hpq
      rw [deleteEdges_adj]
      refine ⟨hHG hpq, fun h => he.2 ?_⟩
      rw [Set.mem_singleton_iff] at h
      rw [← h]
      exact hpq
    · rw [edgeSet_deleteEdges, Set.sdiff_sdiff_comm, Set.ncard_sdiff_singleton_of_mem he]
      omega

/-- **A subgraph of a planar graph is planar.** -/
theorem IsPlanar.mono {G H : SimpleGraph V} (hG : IsPlanar G) (hHG : H ≤ G) : IsPlanar H :=
  IsPlanar.mono_aux _ hG hHG rfl

end Kuratowski
