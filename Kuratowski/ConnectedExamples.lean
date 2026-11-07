import Kuratowski.Connected

/-!
# 연결성 정의의 회귀 예제

블루프린트 정의 `def:conn3`의 작은 예. `scripts/check_blueprint.py`의 `[conn]` 검사와 같은 그래프다.
연결성 자체는 구조 보조정리(`connectedOn_of_clique`, `not_connectedOn_of_isolated`)로 보이고,
커널 계산(`decide`)은 유한한 인접 사실과 명시적인 지지 집합에만 쓴다.

* 별 `K₁,₃`은 2-연결이 아니다. 중심을 지우면 지지 집합이 비므로, 삭제 뒤 지지 집합을 다시 계산하면
  공허하게 이어진 것이 되는 함정을 함께 기록한다.
* 삼각형과 고립점은 2-연결이다 (고립점 수는 연결성에 영향을 주지 않는다).
* `K₄`와 고립점은 3-연결이다.
* 길이 2인 경로는 2-연결이 아니다.
* 블루프린트 `lem:J2`의 반례 그래프(변 `01, 12, 20, 30, 31, 34`)는 2-연결이 아니다.
-/

namespace Kuratowski.ConnectedExamples

open SimpleGraph

/-- 변 목록으로 만든 `Fin n` 위의 단순 그래프 (이 파일의 예제 전용). -/
def graphOf {n : ℕ} (E : List (Fin n × Fin n)) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ((u, v) ∈ E ∨ (v, u) ∈ E)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

instance {n : ℕ} (E : List (Fin n × Fin n)) : DecidableRel (graphOf E).Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- 별 `K₁,₃`: 중심 `0`, 잎 `1, 2, 3`. -/
abbrev star : SimpleGraph (Fin 4) := graphOf [(0, 1), (0, 2), (0, 3)]

/-- 삼각형 `012`와 고립점 `3`. -/
abbrev triangleIso : SimpleGraph (Fin 4) := graphOf [(0, 1), (1, 2), (0, 2)]

/-- `K₄`(`0, 1, 2, 3`)와 고립점 `4`. -/
abbrev k4Iso : SimpleGraph (Fin 5) := graphOf [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- 길이 2인 경로 `0 - 1 - 2`. -/
abbrev path3 : SimpleGraph (Fin 3) := graphOf [(0, 1), (1, 2)]

/-- 블루프린트 `lem:J2`의 반례 그래프: 삼각형 `012`, `3`을 `0`, `1`에 잇고 잎 `4`를 `3`에 잇는다. -/
abbrev j2Graph : SimpleGraph (Fin 5) := graphOf [(0, 1), (1, 2), (2, 0), (3, 0), (3, 1), (3, 4)]

/-! ### 2-연결이 아닌 예 -/

/-- 별은 2-연결이 아니다: 중심 `0`을 지우면 잎 `1`이 고립되어 잎 `2`와 끊긴다. -/
theorem star_not_twoConnected : ¬ TwoConnected star := by
  refine not_connectedOn_of_isolated star 2 star.support {0} (by simp) (u := 1) (v := 2)
    ⟨(mem_support _).2 ⟨0, by decide⟩, by simp⟩
    ⟨(mem_support _).2 ⟨0, by decide⟩, by simp⟩ (by decide) ?_
  rintro w ⟨h, -, hw⟩
  exact (show ∀ w : Fin 4, ¬ (star.Adj 1 w ∧ w ≠ 0) by decide) w ⟨h, hw⟩

/-- 함정: 별에서 중심을 지운 뒤 지지 집합을 다시 계산하면 비어 버린다. 그 집합으로 연결성을 보면
공허하게 참이 되므로, `ConnectedOn`은 지우기 전의 집합에서 지운 점만 뺀다. -/
theorem star_deleteVertices_center_support : (deleteVertices star {0}).support = ∅ := by
  ext v
  simp only [mem_support, deleteVertices_adj, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_exists]
  revert v
  decide

/-- 길이 2인 경로는 2-연결이 아니다: 가운데 `1`을 지우면 `0`이 고립되어 `2`와 끊긴다. -/
theorem path3_not_twoConnected : ¬ TwoConnected path3 := by
  refine not_connectedOn_of_isolated path3 2 path3.support {1} (by simp) (u := 0) (v := 2)
    ⟨(mem_support _).2 ⟨1, by decide⟩, by simp⟩
    ⟨(mem_support _).2 ⟨1, by decide⟩, by simp⟩ (by decide) ?_
  rintro w ⟨h, -, hw⟩
  exact (show ∀ w : Fin 3, ¬ (path3.Adj 0 w ∧ w ≠ 1) by decide) w ⟨h, hw⟩

/-- `lem:J2`의 반례 그래프는 2-연결이 아니다: `3`을 지우면 잎 `4`가 고립되어 `0`과 끊긴다.
그래서 지운 뒤 지지 집합만 보는 약한 가정으로는 `lem:J2`가 거짓이 된다. -/
theorem j2Graph_not_twoConnected : ¬ TwoConnected j2Graph := by
  refine not_connectedOn_of_isolated j2Graph 2 j2Graph.support {3} (by simp) (u := 4) (v := 0)
    ⟨(mem_support _).2 ⟨3, by decide⟩, by simp⟩
    ⟨(mem_support _).2 ⟨1, by decide⟩, by simp⟩ (by decide) ?_
  rintro w ⟨h, -, hw⟩
  exact (show ∀ w : Fin 5, ¬ (j2Graph.Adj 4 w ∧ w ≠ 3) by decide) w ⟨h, hw⟩

/-! ### 연결인 예 (고립점이 있어도 된다) -/

theorem triangleIso_support : triangleIso.support = ↑({0, 1, 2} : Finset (Fin 4)) := by
  ext v
  rw [mem_support, Finset.mem_coe]
  revert v
  decide

/-- 삼각형과 고립점은 2-연결이다. -/
theorem triangleIso_twoConnected : TwoConnected triangleIso := by
  refine connectedOn_of_clique _ 2 _ (le_of_eq ?_) ?_
  · rw [triangleIso_support, Set.ncard_coe_finset]
    rfl
  · rw [triangleIso_support]
    intro u hu v hv huv
    exact (show ∀ u v : Fin 4, u ∈ ({0, 1, 2} : Finset (Fin 4)) → v ∈ ({0, 1, 2} : Finset (Fin 4)) →
      u ≠ v → triangleIso.Adj u v by decide) u v hu hv huv

theorem k4Iso_support : k4Iso.support = ↑({0, 1, 2, 3} : Finset (Fin 5)) := by
  ext v
  rw [mem_support, Finset.mem_coe]
  revert v
  decide

/-- `K₄`와 고립점은 3-연결이다. -/
theorem k4Iso_threeConnected : ThreeConnected k4Iso := by
  refine connectedOn_of_clique _ 3 _ (le_of_eq ?_) ?_
  · rw [k4Iso_support, Set.ncard_coe_finset]
    rfl
  · rw [k4Iso_support]
    intro u hu v hv huv
    exact (show ∀ u v : Fin 5, u ∈ ({0, 1, 2, 3} : Finset (Fin 5)) →
      v ∈ ({0, 1, 2, 3} : Finset (Fin 5)) → u ≠ v → k4Iso.Adj u v by decide) u v hu hv huv

end Kuratowski.ConnectedExamples
