import Kuratowski.Components

/-!
# Vertex connectivity relative to the original support

Blueprint definition `def:conn3`. `deleteVertices G S` keeps the vertex type and deletes only the
edges meeting `S`. `ConnectedOn G k A` means that `k + 1 ≤ A.ncard` and that, after deleting fewer
than `k` vertices, the surviving vertices of the original set `A` are pairwise connected. The
support is not recomputed after deletion. `TwoConnected` and `ThreeConnected` apply this condition
to the original support `G.support`.

The connectivity definitions are used only for finite vertex types. For `k = 0` only the size
condition remains; for positive `k`, deleting fewer than `k` vertices is the blueprint's deletion
of at most `k - 1` vertices.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*}

/-- Delete all edges meeting `S`. Deleted vertices remain in the vertex type as isolated
vertices. -/
def deleteVertices (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h ↦ G.loopless.irrefl _ h.1⟩

@[simp] theorem deleteVertices_adj (G : SimpleGraph V) (S : Set V) (u v : V) :
    (deleteVertices G S).Adj u v ↔ G.Adj u v ∧ u ∉ S ∧ v ∉ S := Iff.rfl

theorem isIsolated_deleteVertices (G : SimpleGraph V) {S : Set V} {v : V} (hv : v ∈ S) :
    (deleteVertices G S).IsIsolated v := fun _ h ↦ h.2.1 hv

theorem deleteVertices_le (G : SimpleGraph V) (S : Set V) : deleteVertices G S ≤ G :=
  fun _ _ h ↦ h.1

@[simp] theorem deleteVertices_empty (G : SimpleGraph V) : deleteVertices G ∅ = G := by
  ext u v
  simp

/-- For finite `V`: the vertices of `A` stay connected after deleting fewer than `k` vertices.
The compared vertices are taken from `A` before deletion, not from the support after deletion. -/
def ConnectedOn [Finite V] (G : SimpleGraph V) (k : ℕ) (A : Set V) : Prop :=
  k + 1 ≤ A.ncard ∧ ∀ S : Set V, S.ncard < k →
    ∀ u ∈ A \ S, ∀ v ∈ A \ S, (deleteVertices G S).Reachable u v

/-- 2-connectivity relative to the original support. The number of isolated vertices is not
restricted. -/
def TwoConnected [Finite V] (G : SimpleGraph V) : Prop := ConnectedOn G 2 G.support

/-- 3-connectivity relative to the original support. The number of isolated vertices is not
restricted. -/
def ThreeConnected [Finite V] (G : SimpleGraph V) : Prop := ConnectedOn G 3 G.support

variable [Finite V]

/-- A clique satisfying the size condition is `k`-connected: after any deletion the surviving
vertices are still pairwise adjacent. -/
theorem connectedOn_of_clique (G : SimpleGraph V) (k : ℕ) (A : Set V)
    (hcard : k + 1 ≤ A.ncard)
    (hclique : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → G.Adj u v) : ConnectedOn G k A := by
  refine ⟨hcard, ?_⟩
  intro S _ u hu v hv
  by_cases huv : u = v
  · subst v
    exact .rfl
  · exact (show (deleteVertices G S).Adj u v from
      ⟨hclique u hu.1 v hv.1 huv, hu.2, hv.2⟩).reachable

/-- If a deletion isolates a surviving vertex while another vertex survives, the set is not
`k`-connected. -/
theorem not_connectedOn_of_isolated (G : SimpleGraph V) (k : ℕ) (A S : Set V)
    (hS : S.ncard < k) {u v : V} (hu : u ∈ A \ S) (hv : v ∈ A \ S) (hne : u ≠ v)
    (hiso : (deleteVertices G S).IsIsolated u) : ¬ ConnectedOn G k A := by
  intro h
  exact hne (eq_of_isIsolated_of_reachable hiso (h.2 S hS u hu v hv)).symm

end Kuratowski
