import Kuratowski.Components

/-!
# 원래 지지 집합을 기준으로 한 꼭짓점 연결성

블루프린트 정의 `def:conn3`. `deleteVertices G S`는 꼭짓점 타입을 바꾸지 않고 `S`에 닿는
변만 지운다. `ConnectedOn G k A`는 `k + 1 ≤ A.ncard`이고, `k`개 미만의 꼭짓점을 지운 뒤에도
원래 집합 `A`에서 살아남은 점들이 서로 이어진다는 뜻이다. 삭제 뒤 지지 집합을 다시 계산하지 않는다.
`TwoConnected`와 `ThreeConnected`는 원래 지지 집합 `G.support`에 이 조건을 적용한다.

연결성 정의는 유한한 꼭짓점 타입에서만 쓴다. `k = 0`에서는 크기 조건만 남으며,
양의 `k`에서는 `k`개 미만 삭제가 블루프린트의 `k - 1`개 이하 삭제와 같다.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*}

/-- `S`에 닿는 변을 모두 지운다. 삭제된 점도 고립점으로서 원래 꼭짓점 타입에 남는다. -/
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

/-- 유한한 `V`에서 `A`의 점들이 `k`개 미만의 꼭짓점 삭제 뒤에도 이어지는 조건.
비교할 점은 삭제 전의 `A`에서 고르며, 삭제 뒤의 지지 집합으로 바꾸지 않는다. -/
def ConnectedOn [Finite V] (G : SimpleGraph V) (k : ℕ) (A : Set V) : Prop :=
  k + 1 ≤ A.ncard ∧ ∀ S : Set V, S.ncard < k →
    ∀ u ∈ A \ S, ∀ v ∈ A \ S, (deleteVertices G S).Reachable u v

/-- 원래 지지 집합을 기준으로 한 2-연결성. 고립점 수에는 제한을 두지 않는다. -/
def TwoConnected [Finite V] (G : SimpleGraph V) : Prop := ConnectedOn G 2 G.support

/-- 원래 지지 집합을 기준으로 한 3-연결성. 고립점 수에는 제한을 두지 않는다. -/
def ThreeConnected [Finite V] (G : SimpleGraph V) : Prop := ConnectedOn G 3 G.support

variable [Finite V]

/-- 크기 조건을 만족하는 클리크는 어떤 삭제 뒤에도 남은 점끼리 인접하므로 `k`-연결이다. -/
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

/-- 삭제 뒤 고립된 점과 다른 생존점이 있으면 `k`-연결이 아니다. -/
theorem not_connectedOn_of_isolated (G : SimpleGraph V) (k : ℕ) (A S : Set V)
    (hS : S.ncard < k) {u v : V} (hu : u ∈ A \ S) (hv : v ∈ A \ S) (hne : u ≠ v)
    (hiso : (deleteVertices G S).IsIsolated u) : ¬ ConnectedOn G k A := by
  intro h
  exact hne (eq_of_isIsolated_of_reachable hiso (h.2 S hS u hu v hv)).symm

end Kuratowski
