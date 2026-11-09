import Kuratowski.SplitVertex

/-!
# 면 경계는 꼭짓점을 반복하지 않는다 (블루프린트 `lem:J1`)

2-연결 그래프의 종수 0 회전 체계에서 한 면 위의 서로 다른 다트는 시작점이 다르다
(`RotationSystem.eq_of_sameCycle_facePerm_of_fst_eq`). 같은 시작점 `w`의 두 다트 `d ≠ e`가 같은 면에
있으면 그 앞의 다트 `φ⁻¹ d`, `φ⁻¹ e`는 같은 면에서 `w`로 들어오는 서로 다른 두 다트다. 그 두 모서리에서
`w`를 쪼개면 (`SplitVertex.lean`) `χ`가 2 늘고, 2-연결성 때문에 `w`를 지워도 두 다트의 시작점이
이어져 연결 조건이 성립하므로 성분 수는 그대로다. 이는 오일러 부등식에 어긋난다.
`d.symm`, `e.symm`을 쓰면 같은 면이라는 보장이 없으므로 앞의 다트를 쓴다.
-/

namespace Kuratowski

open SimpleGraph Equiv Equiv.Perm

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

variable [Finite V] [DecidableEq V]

/-- 블루프린트 `lem:J1`: 2-연결 그래프의 종수 0 회전 체계에서 한 면 위의 서로 다른 다트는 시작점이
다르다. 같은 시작점 `w`를 가진 두 다트 `d ≠ e`가 같은 면에 있으면, 그 앞의 다트 `φ⁻¹ d`, `φ⁻¹ e`는
같은 면에서 `w`로 들어온다. 그 두 모서리에서 `w`를 쪼개면 2-연결성 때문에 연결 조건이 성립하여
오일러 부등식에 모순이다 (`not_splitLinked_of_eulerChar`). -/
theorem eq_of_sameCycle_facePerm_of_fst_eq (hG : TwoConnected G) (R : RotationSystem G)
    (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent) {d e : G.Dart}
    (h : R.facePerm.SameCycle d e) (hfst : d.fst = e.fst) : d = e := by
  by_contra hde
  set e₁ := R.facePerm⁻¹ d with he₁
  set e₂ := R.facePerm⁻¹ e with he₂
  have hd : R.facePerm e₁ = d := by simp [he₁]
  have he : R.facePerm e₂ = e := by simp [he₂]
  have hsnd : e₁.snd = e₂.snd := by
    rw [← R.facePerm_fst e₁, ← R.facePerm_fst e₂, hd, he, hfst]
  have hne : e₁ ≠ e₂ := fun h' ↦ hde (by rw [← hd, ← he, h'])
  have hface : R.facePerm.SameCycle e₁ e₂ := by
    have h' := h
    rw [← hd, ← he, sameCycle_apply_left, sameCycle_apply_right] at h'
    exact h'
  apply not_splitLinked_of_eulerChar hR hsnd hne hface
  refine ⟨e₁.symm, e₂.symm, hsnd, symm_not_mem_splitSet hsnd hne, symm_mem_splitSet, ?_⟩
  -- 2-연결성: `w`를 지워도 `e₁`, `e₂`의 시작점은 이어진다
  have hw1 : e₁.fst ≠ e₂.snd := fun h' ↦ e₁.adj.ne (h'.trans hsnd.symm)
  have hw2 : e₂.fst ≠ e₂.snd := e₂.adj.ne
  exact hG.2 {e₂.snd} (by rw [Set.ncard_singleton]; omega) e₁.fst
    ⟨e₁.adj.mem_support_left, fun h' ↦ hw1 (Set.mem_singleton_iff.1 h')⟩ e₂.fst
    ⟨e₂.adj.mem_support_left, fun h' ↦ hw2 (Set.mem_singleton_iff.1 h')⟩

end RotationSystem

end Kuratowski
