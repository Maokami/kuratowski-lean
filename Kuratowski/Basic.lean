import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Kuratowski.Perm

/-!
# 조합적 평면성: 회전 체계와 오일러 지표

Mathlib에는 그래프의 평면성 정의가 없다. 위상적 정의(ℝ²로의 매장)로 `K₅`의 비평면성을
보이려면 조르당 곡선 정리가 필요한데, 이것도 Mathlib에 없다. 그래서 여기서는 위상 그래프
이론에서 표준으로 쓰는 **조합적 정의**를 쓴다 (Mohar–Thomassen, *Graphs on Surfaces*, 3장).

* 회전 체계(rotation system): 각 꼭짓점에서 나가는 다트(방향 있는 변)들의 순환 순서.
  다트 집합 위의 순열 `rot`으로 표현하며, `rot`은 다트의 시작점을 보존하고 같은 꼭짓점의
  다트들 위에서 하나의 순환을 이룬다.
* 면 순열: `φ d = rot (d.symm)`. 다트 `d = (u, v)`를 따라 `v`에 도착한 뒤, `v`에서
  `(v, u)` 다음 다트로 넘어간다. `φ`의 순환 하나가 면의 경계를 한 바퀴 도는 길이다.
* 회전 체계는 연결 그래프를 닫힌 가향 곡면에 2-세포 매장하는 방법과 (매장의 동형을 무시하면)
  일대일로 대응하고 (Heffter–Edmonds–Ringel 회전 원리), 그 곡면의 종수 `g`는
  `V - E + F = 2 - 2g`로 정해진다. 그래프가 평면 그래프라는 것은 종수 0인 회전 체계가 있다는
  것과 같다.

연결되지 않은 그래프도 다루기 위해 고립점 하나는 면 하나로 세고 (꼭짓점 하나짜리 구면 매장),
평면성을 `V - E + F = 2 · (연결 성분 수)`로 정의한다. 모든 회전 체계에서
`V - E + F ≤ 2 · (연결 성분 수)`이므로 (오일러 부등식, `Kuratowski/Euler.lean`), 이 등식은
"모든 성분이 종수 0"과 같다.

개수는 모두 `Nat.card`와 `Set.ncard`로 센다. 그래서 정의가 `Fintype`, `DecidableRel` 같은
인스턴스에 의존하지 않고, 부분 그래프로 넘어갈 때 인스턴스를 맞출 필요가 없다.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*}

/-- 꼭짓점이 유한하면 다트도 유한하다. -/
instance {G : SimpleGraph V} [Finite V] : Finite G.Dart :=
  Finite.of_injective _ SimpleGraph.Dart.toProd_injective

/-- 그래프 `G`의 회전 체계. -/
structure RotationSystem (G : SimpleGraph V) where
  /-- 각 꼭짓점에서 나가는 다트들의 순환 순서. -/
  rot : Equiv.Perm G.Dart
  /-- `rot`은 다트의 시작점을 보존한다. -/
  fst_rot : ∀ d, (rot d).fst = d.fst
  /-- 같은 꼭짓점에서 나가는 다트들은 `rot`의 한 순환에 들어 있다. -/
  sameCycle_rot : ∀ d d' : G.Dart, d.fst = d'.fst → rot.SameCycle d d'

namespace RotationSystem

variable {G : SimpleGraph V} (R : RotationSystem G)

/-- 면 순열 `φ d = rot (d.symm)`. -/
def facePerm : Equiv.Perm G.Dart :=
  (Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive).trans R.rot

@[simp] lemma facePerm_apply (d : G.Dart) : R.facePerm d = R.rot d.symm := rfl

/-- 면: 면 순열의 순환 하나. -/
abbrev Face := Quotient (Equiv.Perm.SameCycle.setoid R.facePerm)

lemma card_face : Nat.card R.Face = orbitCount R.facePerm := rfl

/-- 면의 개수: 면 순열의 순환 수에 고립점 수를 더한 것. -/
noncomputable def numFaces : ℕ := orbitCount R.facePerm + {v | G.IsIsolated v}.ncard

/-- 오일러 지표 `V - E + F`. -/
noncomputable def eulerChar : ℤ := Nat.card V - G.edgeSet.ncard + R.numFaces

end RotationSystem

/-- 평면 그래프: 오일러 지표가 `2 · (연결 성분 수)`인 회전 체계가 있다. 연결 그래프에서는
`V - E + F = 2`, 즉 종수 0인 회전 체계가 있다는 뜻이다. -/
def IsPlanar (G : SimpleGraph V) : Prop :=
  ∃ R : RotationSystem G, R.eulerChar = 2 * Nat.card G.ConnectedComponent

/-! ## 다트 수와 변 수 -/

lemma card_dart_eq [Finite V] (G : SimpleGraph V) : Nat.card G.Dart = 2 * G.edgeSet.ncard := by
  classical
  have := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, G.dart_card_eq_twice_card_edges, ← coe_edgeFinset,
    Set.ncard_coe_finset]

/-! ## 면 순열의 기본 성질 -/

namespace RotationSystem

variable {G : SimpleGraph V} (R : RotationSystem G)

/-- `rot`이 다트 `d`를 고정하면 `d`의 시작점에서 나가는 다트는 `d` 하나뿐이다. -/
lemma eq_of_rot_eq_self {d : G.Dart} (h : R.rot d = d) {d' : G.Dart} (h' : d'.fst = d.fst) :
    d' = d := by
  obtain ⟨i, hi⟩ := R.sameCycle_rot d d' h'.symm
  rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h i] at hi
  exact hi.symm

/-- 시작점에 `d.snd` 말고 다른 이웃이 있으면 `rot`은 `d`를 고정하지 않는다. -/
lemma rot_ne_self {d : G.Dart} {w : V} (hw : G.Adj d.fst w) (hne : w ≠ d.snd) :
    R.rot d ≠ d := fun h =>
  hne (congrArg (fun x : G.Dart => x.snd) (R.eq_of_rot_eq_self h (d' := ⟨(d.fst, w), hw⟩) rfl))

@[simp] lemma facePerm_fst (d : G.Dart) : (R.facePerm d).fst = d.snd := by
  simp [R.fst_rot]

/-- 단순 그래프에는 고리가 없으므로 길이 1인 면은 없다. -/
lemma facePerm_ne_self (d : G.Dart) : R.facePerm d ≠ d := by
  intro h
  have := congrArg (fun x : G.Dart => x.fst) h
  simp only [facePerm_fst] at this
  exact d.snd_ne_fst this

/-- 도착점에 `d.fst` 말고 다른 이웃이 있으면 `φ (φ d) ≠ d`. 길이 2인 면은 차수 1인 꼭짓점
둘레에서만 생긴다. -/
lemma facePerm_facePerm_ne_self (d : G.Dart) {z : V} (hz : G.Adj d.snd z) (hne : z ≠ d.fst) :
    R.facePerm (R.facePerm d) ≠ d := by
  intro h
  have h1 : (R.facePerm d).snd = d.fst := by
    have := congrArg (fun x : G.Dart => x.fst) h
    simpa only [facePerm_fst] using this
  have hx : R.facePerm d = d.symm := by
    ext
    · simp [R.fst_rot]
    · simpa using h1
  exact R.rot_ne_self (d := d.symm) hz hne hx

end RotationSystem

/-! ## 순환 수 세기 -/

/-- 순열 `f`의 모든 순환의 길이가 `m` 이상이면 `m · (순환 수) ≤ (원소 수)`. -/
lemma mul_orbitCount_le {α : Type*} [Finite α] (f : Equiv.Perm α) (m : ℕ)
    (h : ∀ x k, 0 < k → k < m → (f ^ k) x ≠ x) :
    m * orbitCount f ≤ Nat.card α := by
  classical
  have := Fintype.ofFinite α
  set q : α → Quotient (Equiv.Perm.SameCycle.setoid f) := Quotient.mk _
  unfold orbitCount
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Finset.card_univ (α := α),
    Finset.card_eq_sum_card_fiberwise (f := q) (t := Finset.univ) (fun _ _ => Finset.mem_univ _),
    mul_comm, ← smul_eq_mul, ← Finset.card_univ]
  refine Finset.card_nsmul_le_sum _ _ _ fun c _ => ?_
  set x := c.out
  have key : ∀ i j, i < j → j < m → (f ^ i) x ≠ (f ^ j) x := by
    intro i j hij hj heq
    apply h ((f ^ i) x) (j - i) (Nat.sub_pos_of_lt hij) (by omega)
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hij.le]
    exact heq.symm
  calc m = (Finset.range m).card := (Finset.card_range m).symm
    _ ≤ (Finset.univ.filter fun a => q a = c).card := by
      refine Finset.card_le_card_of_injOn (fun i => (f ^ i) x) ?_ ?_
      · intro i _
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        rw [← Quotient.out_eq c]
        exact Quotient.sound (Equiv.Perm.sameCycle_pow_left.2 (Equiv.Perm.SameCycle.refl f x))
      · intro i hi j hj hij
        simp only [Finset.coe_range, Set.mem_Iio] at hi hj
        rcases lt_trichotomy i j with hlt | heq | hgt
        · exact absurd hij (key i j hlt hj)
        · exact heq
        · exact absurd hij.symm (key j i hgt hi)

end Kuratowski
