import Kuratowski.NonPlanar

/-!
# Planarity is invariant under graph isomorphism

Hence the non-planarity of `K₅` and `K₃,₃` holds for every graph isomorphic to them, independently
of the vertex names (`Fin 5`, `Fin 3 ⊕ Fin 3`).
-/

open SimpleGraph

namespace Kuratowski

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- The bijection of darts induced by a graph isomorphism. -/
def dartEquivOfIso (f : G ≃g H) : G.Dart ≃ H.Dart where
  toFun d := ⟨(f d.fst, f d.snd), f.map_adj_iff.2 d.adj⟩
  invFun d := ⟨(f.symm d.fst, f.symm d.snd), f.symm.map_adj_iff.2 d.adj⟩
  left_inv _ := Dart.ext _ _ (Prod.ext (f.symm_apply_apply _) (f.symm_apply_apply _))
  right_inv _ := Dart.ext _ _ (Prod.ext (f.apply_symm_apply _) (f.apply_symm_apply _))

@[simp] lemma dartEquivOfIso_fst (f : G ≃g H) (d : G.Dart) :
    (dartEquivOfIso f d).fst = f d.fst := rfl

@[simp] lemma dartEquivOfIso_symm_fst (f : G ≃g H) (d : H.Dart) :
    ((dartEquivOfIso f).symm d).fst = f.symm d.fst := rfl

lemma dartEquivOfIso_symm_symm (f : G ≃g H) (d : H.Dart) :
    (dartEquivOfIso f).symm d.symm = ((dartEquivOfIso f).symm d).symm := rfl

namespace RotationSystem

variable [Finite V]

/-- Transport a rotation system along a graph isomorphism. -/
def map (f : G ≃g H) (R : RotationSystem G) : RotationSystem H where
  rot := (dartEquivOfIso f).permCongr R.rot
  fst_rot d := by simp [Equiv.permCongr_apply, R.fst_rot]
  sameCycle_rot d d' h := by
    rw [← (dartEquivOfIso f).apply_symm_apply d, ← (dartEquivOfIso f).apply_symm_apply d',
      sameCycle_permCongr_iff]
    exact R.sameCycle_rot _ _ (by simp [h])

lemma map_facePerm (f : G ≃g H) (R : RotationSystem G) :
    (R.map f).facePerm = (dartEquivOfIso f).permCongr R.facePerm := by
  ext1 d
  simp only [facePerm_apply, map, Equiv.permCongr_apply, dartEquivOfIso_symm_symm]

lemma orbitCount_map (f : G ≃g H) (R : RotationSystem G) :
    orbitCount (R.map f).facePerm = orbitCount R.facePerm := by
  rw [map_facePerm, orbitCount_permCongr]

end RotationSystem

lemma isIsolated_iso_iff (f : G ≃g H) (v : V) : H.IsIsolated (f v) ↔ G.IsIsolated v := by
  constructor
  · intro h u hu
    exact h (f u) (f.map_adj_iff.2 hu)
  · intro h w hw
    apply h (f.symm w)
    rw [← f.map_adj_iff, f.apply_symm_apply]
    exact hw

variable [Finite V]

/-- **Planarity is invariant under graph isomorphism.** -/
theorem IsPlanar.of_iso (f : G ≃g H) (h : IsPlanar G) : IsPlanar H := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R.map f, ?_⟩
  have hV : Nat.card W = Nat.card V := (Nat.card_congr f.toEquiv).symm
  have hE : H.edgeSet.ncard = G.edgeSet.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact (Nat.card_congr f.mapEdgeSet).symm
  have hI : {w | H.IsIsolated w}.ncard = {v | G.IsIsolated v}.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact (Nat.card_congr (f.toEquiv.subtypeEquiv fun v => (isIsolated_iso_iff f v).symm)).symm
  have hC : Nat.card H.ConnectedComponent = Nat.card G.ConnectedComponent :=
    (Nat.card_congr f.connectedComponentEquiv).symm
  unfold RotationSystem.eulerChar RotationSystem.numFaces at hR ⊢
  rw [hV, hE, hI, hC, RotationSystem.orbitCount_map]
  exact hR

omit [Finite V] in
theorem not_isPlanar_of_iso [Finite W] (f : G ≃g H) (h : ¬ IsPlanar G) : ¬ IsPlanar H :=
  fun hH => h (hH.of_iso f.symm)

/-- A graph isomorphic to `K₅` is not planar. -/
theorem not_isPlanar_of_iso_K5 [Finite W] (f : K5 ≃g H) : ¬ IsPlanar H :=
  not_isPlanar_of_iso f K5_not_isPlanar

/-- A graph isomorphic to `K₃,₃` is not planar. -/
theorem not_isPlanar_of_iso_K33 [Finite W] (f : K33 ≃g H) : ¬ IsPlanar H :=
  not_isPlanar_of_iso f K33_not_isPlanar

end Kuratowski
