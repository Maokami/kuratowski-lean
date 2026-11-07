import Kuratowski.Basic
import Kuratowski.Components

/-!
# 꼭짓점 집합 넓히기

블루프린트 보조정리 `lem:map_iff`. `W`, `V`가 유한하고 `f : W ↪ V`가 단사이면
`K.map f`가 평면인 것과 `K`가 평면인 것은 같다 (`isPlanar_map_iff`).

* 다트: `K`의 다트와 `K.map f`의 다트는 `f`로 일대일 대응한다 (`dartEquivMap`). 이 대응은 시작점을
  `f`로 옮기고 다트 뒤집기와 교환한다.
* 회전 체계: 그런 다트 대응을 따라 회전 체계를 양쪽으로 옮긴다 (`RotationSystem.pushDart`,
  `RotationSystem.pullDart`). 면 순열은 켤레라서 순환 수가 같다.
* 수 세기: `f`의 상에 없는 점은 `K.map f`의 고립점이고 혼자 한 성분을 이룬다. 그래서 고립점 수와
  성분 수가 둘 다 `|V| - |W|`만큼 늘어난다 (`ncard_isolated_map_add`, `card_connectedComponent_map_add`).
  `Components.lean`의 `ncard_isolated_map`은 `K`에 고립점이 없는 경우만 다루므로 여기서 일반화한다.
-/

namespace Kuratowski

open SimpleGraph

variable {V W : Type*}

/-! ### 다트 대응을 따라 회전 체계 옮기기 -/

namespace RotationSystem

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- 시작점을 단사 `g`로 옮기는 다트 대응 `e`를 따라 `G`의 회전 체계를 `H`로 옮긴다. -/
def pushDart [Finite V] (R : RotationSystem G) (e : G.Dart ≃ H.Dart) {g : V → W}
    (hg : Function.Injective g) (he : ∀ d, (e d).fst = g d.fst) : RotationSystem H where
  rot := e.permCongr R.rot
  fst_rot d := by rw [Equiv.permCongr_apply, he, R.fst_rot, ← he, Equiv.apply_symm_apply]
  sameCycle_rot d d' h := by
    rw [← e.apply_symm_apply d, ← e.apply_symm_apply d', sameCycle_permCongr_iff]
    have : (e (e.symm d)).fst = (e (e.symm d')).fst := by simp [h]
    rw [he, he] at this
    exact R.sameCycle_rot _ _ (hg this)

/-- 같은 다트 대응을 거꾸로 따라 `H`의 회전 체계를 `G`로 옮긴다. -/
def pullDart [Finite W] (S : RotationSystem H) (e : G.Dart ≃ H.Dart) {g : V → W}
    (hg : Function.Injective g) (he : ∀ d, (e d).fst = g d.fst) : RotationSystem G where
  rot := e.symm.permCongr S.rot
  fst_rot d := by
    apply hg
    rw [← he, ← he, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply, S.fst_rot]
  sameCycle_rot d d' h := by
    rw [← e.symm_apply_apply d, ← e.symm_apply_apply d', sameCycle_permCongr_iff]
    exact S.sameCycle_rot _ _ (by rw [he, he, h])

variable (e : G.Dart ≃ H.Dart) {g : V → W} (hg : Function.Injective g)
  (he : ∀ d, (e d).fst = g d.fst) (hsymm : ∀ d, e d.symm = (e d).symm)
include hsymm

omit hsymm in
private lemma symm_apply_symm (hsymm : ∀ d, e d.symm = (e d).symm) (x : H.Dart) :
    e.symm x.symm = (e.symm x).symm := by
  rw [Equiv.symm_apply_eq, hsymm, Equiv.apply_symm_apply]

lemma pushDart_facePerm [Finite V] (R : RotationSystem G) :
    (R.pushDart e hg he).facePerm = e.permCongr R.facePerm := by
  ext1 x
  simp only [facePerm_apply, pushDart, Equiv.permCongr_apply, symm_apply_symm e hsymm]

lemma pullDart_facePerm [Finite W] (S : RotationSystem H) :
    (S.pullDart e hg he).facePerm = e.symm.permCongr S.facePerm := by
  ext1 d
  simp only [facePerm_apply, pullDart, Equiv.permCongr_apply, Equiv.symm_symm, hsymm]

lemma orbitCount_pushDart [Finite V] (R : RotationSystem G) :
    orbitCount (R.pushDart e hg he).facePerm = orbitCount R.facePerm := by
  rw [pushDart_facePerm e hg he hsymm, orbitCount_permCongr]

lemma orbitCount_pullDart [Finite W] (S : RotationSystem H) :
    orbitCount (S.pullDart e hg he).facePerm = orbitCount S.facePerm := by
  rw [pullDart_facePerm e hg he hsymm, orbitCount_permCongr]

end RotationSystem

/-! ### `K.map f`의 다트 -/

variable (K : SimpleGraph W) (f : W ↪ V)

/-- `K`의 다트 `(a, b)`를 `K.map f`의 다트 `(f a, f b)`로 보낸다. -/
def dartMap (d : K.Dart) : (K.map f).Dart :=
  ⟨(f d.fst, f d.snd), map_adj_apply.2 d.adj⟩

theorem dartMap_bijective : Function.Bijective (dartMap K f) := by
  constructor
  · intro d d' h
    have h' := congrArg Dart.toProd h
    simp only [dartMap, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h'
    exact Dart.ext _ _ (Prod.ext h'.1 h'.2)
  · intro x
    obtain ⟨a, b, hab, ha, hb⟩ := (map_adj f K _ _).1 x.adj
    exact ⟨⟨(a, b), hab⟩, Dart.ext _ _ (Prod.ext ha hb)⟩

/-- `K`의 다트와 `K.map f`의 다트의 일대일 대응. -/
noncomputable def dartEquivMap : K.Dart ≃ (K.map f).Dart :=
  Equiv.ofBijective _ (dartMap_bijective K f)

@[simp] theorem dartEquivMap_fst (d : K.Dart) : (dartEquivMap K f d).fst = f d.fst := rfl

theorem dartEquivMap_symm (d : K.Dart) : dartEquivMap K f d.symm = (dartEquivMap K f d).symm :=
  rfl

/-! ### 고립점과 연결 성분 세기 -/

theorem isIsolated_map_apply {a : W} : (K.map f).IsIsolated (f a) ↔ K.IsIsolated a := by
  constructor
  · intro h b hab
    exact h (f b) (map_adj_apply.2 hab)
  · intro h v hv
    obtain ⟨a', b, hab, ha', rfl⟩ := (map_adj f K _ _).1 hv
    rw [f.injective ha'] at hab
    exact h b hab

/-- `f`의 상에 없는 점은 `K.map f`의 고립점이다. -/
theorem isIsolated_map_of_notMem {v : V} (hv : v ∉ Set.range f) : (K.map f).IsIsolated v := by
  intro w hw
  obtain ⟨a, -, -, rfl, -⟩ := (map_adj f K _ _).1 hw
  exact hv ⟨a, rfl⟩

/-- 고립점 수: `f`의 상에 없는 `|V| - |W|`개의 점이 고립점으로 더해진다. `K`에 고립점이 있어도 된다. -/
theorem ncard_isolated_map_add [Finite V] [Finite W] :
    {v | (K.map f).IsIsolated v}.ncard + Nat.card W =
      {a | K.IsIsolated a}.ncard + Nat.card V := by
  have hS : {v | (K.map f).IsIsolated v} = f '' {a | K.IsIsolated a} ∪ (Set.range f)ᶜ := by
    ext v
    by_cases hv : v ∈ Set.range f
    · obtain ⟨a, rfl⟩ := hv
      simp [isIsolated_map_apply]
    · simp [isIsolated_map_of_notMem K f hv, hv]
  have hdisj : Disjoint (f '' {a | K.IsIsolated a}) (Set.range f)ᶜ :=
    Set.disjoint_compl_right_iff_subset.2 (Set.image_subset_range _ _)
  rw [hS, Set.ncard_union_eq hdisj, Set.ncard_image_of_injective _ f.injective]
  have h1 := Set.ncard_add_ncard_compl (Set.range f)
  have h2 := Set.ncard_range_of_injective f.injective
  omega

/-- `K.map f`에서 `f a`와 `f b`가 이어진 것은 `K`에서 `a`와 `b`가 이어진 것과 같다. -/
theorem reachable_map_apply {a b : W} : (K.map f).Reachable (f a) (f b) ↔ K.Reachable a b := by
  constructor
  · intro h
    have : Nonempty W := ⟨a⟩
    -- `f`의 왼쪽 역함수는 `K.map f`에서 `K`로 가는 그래프 준동형이다.
    let g : K.map f →g K :=
      { toFun := Function.invFun f
        map_rel' := fun {u v} huv ↦ by
          obtain ⟨u', v', h, rfl, rfl⟩ := (map_adj f K _ _).1 huv
          simpa [Function.leftInverse_invFun f.injective _] using h }
    simpa [g, Function.leftInverse_invFun f.injective _] using h.map g
  · intro h
    exact h.map (Embedding.map f K).toHom

/-- 연결 성분 수: `f`의 상에 없는 `|V| - |W|`개의 점이 각각 한 성분으로 더해진다. -/
theorem card_connectedComponent_map_add [Finite V] [Finite W] :
    Nat.card (K.map f).ConnectedComponent + Nat.card W =
      Nat.card K.ConnectedComponent + Nat.card V := by
  let φ : K.ConnectedComponent → (K.map f).ConnectedComponent :=
    ConnectedComponent.map (Embedding.map f K).toHom
  let ψ : ((Set.range f)ᶜ : Set V) → (K.map f).ConnectedComponent :=
    fun v ↦ (K.map f).connectedComponentMk v
  have hφ (a : W) : φ (K.connectedComponentMk a) = (K.map f).connectedComponentMk (f a) := rfl
  -- 상에 없는 점은 고립점이라 자기 자신하고만 이어져 있다.
  have hout (v : ((Set.range f)ᶜ : Set V)) (w : V) (h : (K.map f).Reachable v w) : w = v :=
    eq_of_isIsolated_of_reachable (isIsolated_map_of_notMem K f v.2) h
  have hbij : Function.Bijective (Sum.elim φ ψ) := by
    constructor
    · rintro (c | v) (c' | v') h
      · induction c using ConnectedComponent.ind with | h a => ?_
        induction c' using ConnectedComponent.ind with | h b => ?_
        simp only [Sum.elim_inl, hφ, ConnectedComponent.eq, reachable_map_apply] at h
        exact congrArg Sum.inl (ConnectedComponent.eq.2 h)
      · induction c using ConnectedComponent.ind with | h a => ?_
        simp only [Sum.elim_inl, Sum.elim_inr, hφ, ψ, ConnectedComponent.eq] at h
        exact absurd ⟨a, hout v' _ h.symm⟩ v'.2
      · induction c' using ConnectedComponent.ind with | h b => ?_
        simp only [Sum.elim_inl, Sum.elim_inr, hφ, ψ, ConnectedComponent.eq] at h
        exact absurd ⟨b, hout v _ h⟩ v.2
      · simp only [Sum.elim_inr, ψ, ConnectedComponent.eq] at h
        exact congrArg Sum.inr (Subtype.ext (hout v _ h).symm)
    · intro c
      induction c using ConnectedComponent.ind with | h v => ?_
      by_cases hv : v ∈ Set.range f
      · obtain ⟨a, rfl⟩ := hv
        exact ⟨Sum.inl (K.connectedComponentMk a), hφ a⟩
      · exact ⟨Sum.inr ⟨v, hv⟩, rfl⟩
  have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_sum] at hcard
  have h1 := Set.ncard_add_ncard_compl (Set.range f)
  have h2 := Set.ncard_range_of_injective f.injective
  rw [Nat.card_coe_set_eq] at hcard
  omega

/-! ### 평면성 -/

/-- **꼭짓점 집합 넓히기** (블루프린트 `lem:map_iff`). `W`, `V`가 유한하고 `f : W ↪ V`이면
`K.map f`가 평면인 것과 `K`가 평면인 것은 같다. -/
theorem isPlanar_map_iff [Finite V] [Finite W] : IsPlanar (K.map f) ↔ IsPlanar K := by
  have hE := ncard_edgeSet_map K f
  have hI := ncard_isolated_map_add K f
  have hC := card_connectedComponent_map_add K f
  have he : ∀ d, (dartEquivMap K f d).fst = f d.fst := fun _ ↦ rfl
  have hs : ∀ d, dartEquivMap K f d.symm = (dartEquivMap K f d).symm := dartEquivMap_symm K f
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S.pullDart (dartEquivMap K f) f.injective he, ?_⟩
    have hO := S.orbitCount_pullDart (dartEquivMap K f) f.injective he hs
    unfold RotationSystem.eulerChar RotationSystem.numFaces at hS ⊢
    rw [hO]
    push_cast at hS ⊢
    omega
  · rintro ⟨R, hR⟩
    refine ⟨R.pushDart (dartEquivMap K f) f.injective he, ?_⟩
    have hO := R.orbitCount_pushDart (dartEquivMap K f) f.injective he hs
    unfold RotationSystem.eulerChar RotationSystem.numFaces at hR ⊢
    rw [hO]
    push_cast at hR ⊢
    omega

end Kuratowski
