import Kuratowski.Basic
import Kuratowski.Components

/-!
# Enlarging the vertex set

Blueprint lemma `lem:map_iff`. If `W` and `V` are finite and `f : W ↪ V` is injective, then
`K.map f` is planar iff `K` is planar (`isPlanar_map_iff`).

* Darts: `f` gives a bijection between the darts of `K` and those of `K.map f` (`dartEquivMap`).
  It maps start vertices along `f` and commutes with dart reversal.
* Rotation systems: we transport rotation systems both ways along such a dart bijection
  (`RotationSystem.pushDart`, `RotationSystem.pullDart`). The face permutations are conjugate, so
  they have the same number of cycles.
* Counting: a vertex outside the range of `f` is isolated in `K.map f` and forms a component by
  itself. Hence the numbers of isolated vertices and of components both increase by `|V| - |W|`
  (`ncard_isolated_map_add`, `card_connectedComponent_map_add`). `ncard_isolated_map` in
  `Components.lean` covers only the case where `K` has no isolated vertices; here we generalize it.
-/

namespace Kuratowski

open SimpleGraph

variable {V W : Type*}

/-! ### Transporting rotation systems along a dart bijection -/

namespace RotationSystem

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Transport a rotation system of `G` to `H` along a dart bijection `e` that maps start vertices
by the injection `g`. -/
def pushDart [Finite V] (R : RotationSystem G) (e : G.Dart ≃ H.Dart) {g : V → W}
    (hg : Function.Injective g) (he : ∀ d, (e d).fst = g d.fst) : RotationSystem H where
  rot := e.permCongr R.rot
  fst_rot d := by rw [Equiv.permCongr_apply, he, R.fst_rot, ← he, Equiv.apply_symm_apply]
  sameCycle_rot d d' h := by
    rw [← e.apply_symm_apply d, ← e.apply_symm_apply d', sameCycle_permCongr_iff]
    have : (e (e.symm d)).fst = (e (e.symm d')).fst := by simp [h]
    rw [he, he] at this
    exact R.sameCycle_rot _ _ (hg this)

/-- Transport a rotation system of `H` back to `G` along the same dart bijection. -/
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

/-! ### Darts of `K.map f` -/

variable (K : SimpleGraph W) (f : W ↪ V)

/-- Send a dart `(a, b)` of `K` to the dart `(f a, f b)` of `K.map f`. -/
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

/-- The bijection between the darts of `K` and the darts of `K.map f`. -/
noncomputable def dartEquivMap : K.Dart ≃ (K.map f).Dart :=
  Equiv.ofBijective _ (dartMap_bijective K f)

@[simp] theorem dartEquivMap_fst (d : K.Dart) : (dartEquivMap K f d).fst = f d.fst := rfl

theorem dartEquivMap_symm (d : K.Dart) : dartEquivMap K f d.symm = (dartEquivMap K f d).symm :=
  rfl

/-! ### Counting isolated vertices and connected components -/

theorem isIsolated_map_apply {a : W} : (K.map f).IsIsolated (f a) ↔ K.IsIsolated a := by
  constructor
  · intro h b hab
    exact h (f b) (map_adj_apply.2 hab)
  · intro h v hv
    obtain ⟨a', b, hab, ha', rfl⟩ := (map_adj f K _ _).1 hv
    rw [f.injective ha'] at hab
    exact h b hab

/-- A vertex outside the range of `f` is isolated in `K.map f`. -/
theorem isIsolated_map_of_notMem {v : V} (hv : v ∉ Set.range f) : (K.map f).IsIsolated v := by
  intro w hw
  obtain ⟨a, -, -, rfl, -⟩ := (map_adj f K _ _).1 hw
  exact hv ⟨a, rfl⟩

/-- Isolated vertices: the `|V| - |W|` vertices outside the range of `f` are added as isolated
vertices. `K` may have isolated vertices. -/
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

/-- `f a` and `f b` are connected in `K.map f` iff `a` and `b` are connected in `K`. -/
theorem reachable_map_apply {a b : W} : (K.map f).Reachable (f a) (f b) ↔ K.Reachable a b := by
  constructor
  · intro h
    have : Nonempty W := ⟨a⟩
    -- A left inverse of `f` is a graph homomorphism from `K.map f` to `K`.
    let g : K.map f →g K :=
      { toFun := Function.invFun f
        map_rel' := fun {u v} huv ↦ by
          obtain ⟨u', v', h, rfl, rfl⟩ := (map_adj f K _ _).1 huv
          simpa [Function.leftInverse_invFun f.injective _] using h }
    simpa [g, Function.leftInverse_invFun f.injective _] using h.map g
  · intro h
    exact h.map (Embedding.map f K).toHom

/-- Connected components: each of the `|V| - |W|` vertices outside the range of `f` adds one
component. -/
theorem card_connectedComponent_map_add [Finite V] [Finite W] :
    Nat.card (K.map f).ConnectedComponent + Nat.card W =
      Nat.card K.ConnectedComponent + Nat.card V := by
  let φ : K.ConnectedComponent → (K.map f).ConnectedComponent :=
    ConnectedComponent.map (Embedding.map f K).toHom
  let ψ : ((Set.range f)ᶜ : Set V) → (K.map f).ConnectedComponent :=
    fun v ↦ (K.map f).connectedComponentMk v
  have hφ (a : W) : φ (K.connectedComponentMk a) = (K.map f).connectedComponentMk (f a) := rfl
  -- A vertex outside the range is isolated, so it is connected only to itself.
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

/-! ### Planarity -/

/-- **Enlarging the vertex set** (blueprint `lem:map_iff`). If `W` and `V` are finite and
`f : W ↪ V`, then `K.map f` is planar iff `K` is planar. -/
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
