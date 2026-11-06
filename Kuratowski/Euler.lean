import Kuratowski.Deletion
import Kuratowski.Components

/-!
# 오일러 부등식과 부분 그래프

* **오일러 부등식** (`RotationSystem.eulerChar_le`): 모든 회전 체계에서
  `V - E + F ≤ 2 · (연결 성분 수)`. 변의 수에 대한 귀납법으로 보인다. 변 `uv`를 지우면
  - `uv`의 두 다트가 같은 면에 있을 때: `F`가 1 늘어 오일러 지표가 2 늘고, 성분은 많아야 하나 는다.
  - 다른 면에 있을 때: `F`가 1 줄어 오일러 지표는 그대로이고, `uv`가 다리가 아니므로 성분 수도
    그대로다.
* **부분 그래프** (`IsPlanar.mono`): 평면 그래프의 부분 그래프는 평면 그래프다. 위와 같은 계산에
  오일러 부등식을 더하면 변 하나를 지워도 평면성이 유지되고, 이것을 반복한다.
-/

namespace Kuratowski

open Equiv Equiv.Perm SimpleGraph

variable {V : Type*} [Finite V] [DecidableEq V]

namespace RotationSystem

omit [Finite V] [DecidableEq V] in
/-- 변이 없는 그래프에서는 `V - E + F = 2V = 2c`. -/
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

/-- 변 `uv`를 지운 뒤의 오일러 지표: 두 다트가 같은 면에 있으면 2 는다. -/
lemma eulerChar_del_of_sameCycle {G : SimpleGraph V} (R : RotationSystem G) (d : G.Dart)
    (h : SameCycle R.facePerm d d.symm) : (R.del d).eulerChar = R.eulerChar + 2 := by
  have hE : (G.deleteEdges {d.edge}).edgeSet.ncard + 1 = G.edgeSet.ncard :=
    ncard_edgeSet_deleteEdges G d.adj
  have := R.numFaces_del_of_sameCycle d h
  unfold eulerChar
  rw [this]
  push_cast
  omega

/-- 변 `uv`를 지운 뒤의 오일러 지표: 두 다트가 다른 면에 있으면 그대로다. -/
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

/-- **오일러 부등식**: 모든 회전 체계에서 `V - E + F ≤ 2 · (연결 성분 수)`. -/
theorem eulerChar_le {G : SimpleGraph V} (R : RotationSystem G) :
    R.eulerChar ≤ 2 * Nat.card G.ConnectedComponent :=
  eulerChar_le_aux _ R rfl

end RotationSystem

/-- 평면 그래프에서 변 하나를 지워도 평면 그래프다. -/
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

/-- **평면 그래프의 부분 그래프는 평면 그래프다.** -/
theorem IsPlanar.mono {G H : SimpleGraph V} (hG : IsPlanar G) (hHG : H ≤ G) : IsPlanar H :=
  IsPlanar.mono_aux _ hG hHG rfl

end Kuratowski
