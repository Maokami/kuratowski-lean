import Kuratowski.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# 정의가 공허하지 않음을 확인: `K₄`는 평면 그래프다

`IsPlanar`가 아무 그래프에도 성립하지 않는 정의라면 `K₅`의 비평면성은 의미가 없다.
그래서 `K₄`에 오일러 지표가 2인 회전 체계를 실제로 만들어 보인다.

`K₄`를 평면에 그리면 면이 4개다 (`4 - 6 + 4 = 2`). 회전은 다음과 같다.
꼭짓점 0, 2에서는 나머지 이웃을 번호가 커지는 순환 순서로, 1, 3에서는 작아지는 순서로 돈다.
-/

open Finset SimpleGraph

namespace Kuratowski

/-! ## 면을 직접 세는 보조정리 -/

/-- 순환마다 서로 다른 이름표를 붙일 수 있으면, 순환 수는 이름표 수와 같다. -/
lemma card_quotient_sameCycle_eq {α β : Type*} [Finite α] (f : Equiv.Perm α) (lab : α → β)
    (hinv : ∀ x, lab (f x) = lab x) (hsame : ∀ x y, lab x = lab y → f.SameCycle x y)
    (hsurj : Function.Surjective lab) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid f)) = Nat.card β := by
  have hpow : ∀ (n : ℕ) x, lab ((f ^ n) x) = lab x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro x; rw [pow_succ', Equiv.Perm.mul_apply, hinv, ih]
  refine Nat.card_eq_of_bijective
    (Quotient.lift lab fun a b (hab : f.SameCycle a b) => ?_) ⟨?_, ?_⟩
  · obtain ⟨n, hn⟩ := hab.exists_nat_pow_eq
    rw [← hn, hpow]
  · rintro ⟨a⟩ ⟨b⟩ h
    exact Quotient.sound (hsame a b h)
  · intro c
    obtain ⟨a, rfl⟩ := hsurj c
    exact ⟨⟦a⟧, rfl⟩

lemma card_connectedComponent_eq_one {V : Type*} {G : SimpleGraph V} (h : G.Connected) :
    Nat.card G.ConnectedComponent = 1 := by
  have := h.preconnected.subsingleton_connectedComponent
  have : Nonempty G.ConnectedComponent := h.nonempty.map G.connectedComponentMk
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩

/-! ## `K₄`의 회전 체계 -/

/-- 완전 그래프 `K₄`. -/
abbrev K4 : SimpleGraph (Fin 4) := ⊤

/-- 꼭짓점 `v` 둘레에서 이웃 `w` 다음에 오는 이웃. (`v`는 자기 자신으로 보낸다.) -/
def nxt : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 2, 3, 1], ![3, 1, 0, 2], ![1, 3, 2, 0], ![2, 0, 1, 3]]

/-- `nxt v`의 역. -/
def prv : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 3, 1, 2], ![2, 1, 3, 0], ![3, 0, 2, 1], ![1, 2, 0, 3]]

lemma nxt_adj : ∀ v w : Fin 4, v ≠ w → v ≠ nxt v w := by decide
lemma prv_adj : ∀ v w : Fin 4, v ≠ w → v ≠ prv v w := by decide
lemma prv_nxt : ∀ v w : Fin 4, prv v (nxt v w) = w := by decide
lemma nxt_prv : ∀ v w : Fin 4, nxt v (prv v w) = w := by decide

/-- `K₄`의 다트 위의 회전. -/
def k4Rot : Equiv.Perm K4.Dart where
  toFun d := ⟨(d.fst, nxt d.fst d.snd), (top_adj _ _).2 (nxt_adj _ _ d.adj.ne)⟩
  invFun d := ⟨(d.fst, prv d.fst d.snd), (top_adj _ _).2 (prv_adj _ _ d.adj.ne)⟩
  left_inv _ := Dart.ext _ _ (Prod.ext rfl (prv_nxt _ _))
  right_inv _ := Dart.ext _ _ (Prod.ext rfl (nxt_prv _ _))

/-- `K₄`의 평면 회전 체계. -/
def k4RotationSystem : RotationSystem K4 where
  rot := k4Rot
  fst_rot _ := rfl
  sameCycle_rot := by
    have : ∀ d d' : K4.Dart, d.fst = d'.fst → ∃ i : Fin 3, (k4Rot ^ (i : ℕ)) d = d' := by
      decide +kernel
    intro d d' h
    obtain ⟨i, hi⟩ := this d d' h
    exact ⟨i, by simpa using hi⟩

/-- 면 이름표: `K₄`의 네 면은 `{01, 13, 30}`, `{02, 21, 10}`, `{03, 32, 20}`, `{12, 23, 31}`. -/
def k4FaceLabel (d : K4.Dart) : Fin 4 :=
  ![![0, 0, 1, 2], ![1, 0, 3, 0], ![2, 1, 0, 3], ![0, 3, 2, 0]] d.fst d.snd

lemma k4_card_face : Nat.card k4RotationSystem.Face = 4 := by
  rw [card_quotient_sameCycle_eq k4RotationSystem.facePerm k4FaceLabel, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  · decide +kernel
  · intro x y h
    have : ∀ x y : K4.Dart, k4FaceLabel x = k4FaceLabel y →
        ∃ i : Fin 3, (k4RotationSystem.facePerm ^ (i : ℕ)) x = y := by
      decide +kernel
    obtain ⟨i, hi⟩ := this x y h
    exact ⟨i, by simpa using hi⟩
  · have : ∀ c : Fin 4, ∃ d : K4.Dart, k4FaceLabel d = c := by decide +kernel
    exact this

/-- **`K₄`는 평면 그래프다.** 따라서 `IsPlanar`는 공허한 정의가 아니다. -/
theorem K4_isPlanar : IsPlanar K4 := by
  refine ⟨k4RotationSystem, ?_⟩
  have hV : Nat.card (Fin 4) = 4 := by simp
  have hE : K4.edgeSet.ncard = 6 := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two]
    rfl
  have hI : {v | K4.IsIsolated v}.ncard = 0 := by
    rw [Set.ncard_eq_zero]
    refine Set.eq_empty_of_forall_notMem fun v => ?_
    unfold IsIsolated
    revert v
    decide
  have hC : Nat.card K4.ConnectedComponent = 1 := card_connectedComponent_eq_one connected_top
  have hF : orbitCount k4RotationSystem.facePerm = 4 := k4_card_face
  unfold RotationSystem.eulerChar RotationSystem.numFaces
  rw [hF, hV, hE, hI, hC]
  norm_num

end Kuratowski
