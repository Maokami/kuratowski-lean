import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ZMod.Basic

/-!
# 사이클의 순환 꼭짓점 수열

블루프린트 정의 `def:cycseq`. 길이가 적어도 3인 단사 수열 `ZMod m → V`에서 이웃한 위치의
꼭짓점들이 인접한다. 인덱스는 모듈러 덧셈을 쓰므로 마지막 위치와 첫 위치의 인접도 포함한다.
시작점을 옮기는 `rotate`와 방향을 바꾸는 `reverse`를 제공한다. 유도 사이클일 필요는 없다.

호를 Mathlib `Walk`와 연결하고 내부의 서로소성을 증명하는 작업은 경로 체계의 후속 단위다.
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {m : ℕ}

/-- 단사인 순환 꼭짓점 수열. 사이클의 길이는 적어도 3이다. -/
structure CyclicSequence (G : SimpleGraph V) (m : ℕ) where
  length_ge_three : 3 ≤ m
  vertex : ZMod m ↪ V
  adj_next : ∀ i, G.Adj (vertex i) (vertex (i + 1))

namespace CyclicSequence

instance : CoeFun (CyclicSequence G m) (fun _ ↦ ZMod m → V) := ⟨fun C ↦ C.vertex⟩

theorem injective (C : CyclicSequence G m) : Function.Injective C := C.vertex.injective

@[simp] theorem apply_eq_iff (C : CyclicSequence G m) (i j : ZMod m) : C i = C j ↔ i = j :=
  C.injective.eq_iff

theorem length_pos (C : CyclicSequence G m) : 0 < m := by
  have := C.length_ge_three
  omega

/-- `ZMod m`의 유한 인스턴스가 필요한 곳에서 쓸 양의 길이 조건. -/
theorem neZero (C : CyclicSequence G m) : NeZero m := ⟨Nat.ne_of_gt C.length_pos⟩

@[ext] theorem ext {C D : CyclicSequence G m} (h : ∀ i, C i = D i) : C = D := by
  have hvertex : C.vertex = D.vertex := Function.Embedding.ext h
  cases C
  cases D
  cases hvertex
  rfl

theorem ne_next (C : CyclicSequence G m) (i : ZMod m) : C i ≠ C (i + 1) :=
  (C.adj_next i).ne

/-- 마지막 위치 `-1`과 첫 위치 `0`의 인접은 순환 수열의 인접 조건에서 나온다. -/
theorem adj_last_zero (C : CyclicSequence G m) : G.Adj (C (-1)) (C 0) := by
  simpa using C.adj_next (-1)

/-- 시작점을 `a`만큼 옮긴 같은 순환 수열. -/
def rotate (C : CyclicSequence G m) (a : ZMod m) : CyclicSequence G m where
  length_ge_three := C.length_ge_three
  vertex := ⟨fun i ↦ C (i + a), fun _ _ h ↦ add_right_cancel (C.injective h)⟩
  adj_next i := by simpa [add_assoc, add_comm, add_left_comm] using C.adj_next (i + a)

@[simp] theorem rotate_apply (C : CyclicSequence G m) (a i : ZMod m) :
    C.rotate a i = C (i + a) := rfl

/-- 위치 `0`을 고정하고 순환 방향을 뒤집는다. -/
def reverse (C : CyclicSequence G m) : CyclicSequence G m where
  length_ge_three := C.length_ge_three
  vertex := ⟨fun i ↦ C (-i), fun _ _ h ↦ neg_injective (C.injective h)⟩
  adj_next i := by
    change G.Adj (C (-i)) (C (-(i + 1)))
    simpa using (C.adj_next (-(i + 1))).symm

@[simp] theorem reverse_apply (C : CyclicSequence G m) (i : ZMod m) :
    C.reverse i = C (-i) := rfl

@[simp] theorem rotate_zero (C : CyclicSequence G m) : C.rotate 0 = C := by
  ext i
  simp

@[simp] theorem reverse_reverse (C : CyclicSequence G m) : C.reverse.reverse = C := by
  ext i
  simp

/-- 길이가 0, 1, 2인 수열은 사이클로 허용하지 않는다. -/
theorem not_nonempty_of_lt_three (h : m < 3) : ¬ Nonempty (CyclicSequence G m) := by
  rintro ⟨C⟩
  have := C.length_ge_three
  omega

/-- 변이 없는 그래프에는 이런 순환 수열이 없다. -/
theorem not_nonempty_bot : ¬ Nonempty (CyclicSequence (⊥ : SimpleGraph V) m) := by
  rintro ⟨C⟩
  exact C.adj_next 0

/-- 삼각형의 순환 수열: `0 → 1 → 2 → 0`. -/
def triangle : CyclicSequence (⊤ : SimpleGraph (ZMod 3)) 3 where
  length_ge_three := by decide
  vertex := Function.Embedding.refl _
  adj_next := by decide +kernel

/-- 마지막 위치의 다음은 첫 위치다. 마지막 변을 빠뜨린 열린 경로가 아님을 확인한다. -/
theorem triangle_closing_edge :
    (⊤ : SimpleGraph (ZMod 3)).Adj (triangle 2) (triangle 0) := by
  have hwrap : (2 : ZMod 3) + 1 = 0 := by decide
  simpa only [hwrap] using triangle.adj_next (2 : ZMod 3)

end CyclicSequence

end Kuratowski
