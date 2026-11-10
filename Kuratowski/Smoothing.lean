import Kuratowski.Basic
import Kuratowski.Components

/-!
# Reversing an edge subdivision

`H₂ = subdivideEdge H x y w` replaces an edge `xy` by `xw` and `wy`, where `w`
is isolated in `H`. If `H₂` is planar, so is `H` (`IsPlanar.of_subdivideEdge`).

Starting from a rotation system on `H₂`, remove the darts `(w, x)` and `(w, y)`
and rename `(x, w)`, `(y, w)` to `(x, y)`, `(y, x)`. The face permutation skips
the removed darts, preserving its orbit count. The vertex `w` becomes isolated,
so the total face and component counts each increase by one, while the edge count
decreases by one. Thus the equation `|V| - |E| + |F| = 2c` is preserved.
-/

namespace Kuratowski

open Equiv Equiv.Perm SimpleGraph

variable {V : Type*} [DecidableEq V] {H : SimpleGraph V} {x y w : V}

namespace Smooth

/-- Endpoint in `H` corresponding to a dart `(p, q)` of `H₂` with `p ≠ w`. -/
def tgt (x y w p q : V) : V := if q = w then (if p = x then y else x) else q

/-- Endpoint in `H₂` corresponding to a dart `(p, q)` of `H`. -/
def src (x y w p q : V) : V := if s(p, q) = s(x, y) then w else q

section Adj

variable (hxy : H.Adj x y) (hw : H.IsIsolated w)
include hxy hw

omit [DecidableEq V] in
lemma x_ne_w : x ≠ w := (ne_of_subdivide hxy hw).1

omit [DecidableEq V] in
lemma w_ne_y : w ≠ y := (ne_of_subdivide hxy hw).2

omit [DecidableEq V] in
lemma adj_w_iff {z : V} : (subdivideEdge H x y w).Adj w z ↔ z = x ∨ z = y := by
  rw [subdivideEdge_adj (x_ne_w hxy hw) (w_ne_y hxy hw)]
  constructor
  · rintro (⟨h, _⟩ | h | h)
    · exact (hw z h).elim
    · rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd h1.symm (x_ne_w hxy hw)
      · exact Or.inl h2
    · rcases Sym2.eq_iff.1 h with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact Or.inr h2
      · exact absurd h1 (w_ne_y hxy hw)
  · rintro (h | h) <;> rw [h]
    · exact Or.inr (Or.inl Sym2.eq_swap)
    · exact Or.inr (Or.inr rfl)

omit [DecidableEq V] in
lemma adj_ne_w_iff {p q : V} (hp : p ≠ w) (hq : q ≠ w) :
    (subdivideEdge H x y w).Adj p q ↔ H.Adj p q ∧ s(p, q) ≠ s(x, y) := by
  rw [subdivideEdge_adj (x_ne_w hxy hw) (w_ne_y hxy hw)]
  constructor
  · rintro (h | h | h)
    · exact h
    · rcases Sym2.eq_iff.1 h with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact absurd h2 hq
      · exact absurd h1 hp
    · rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd h1 hp
      · exact absurd h2 hq
  · exact Or.inl

omit [DecidableEq V] hxy in
lemma fst_ne_w (a : H.Dart) : a.fst ≠ w := fun h => hw a.snd (h ▸ a.adj)

omit [DecidableEq V] hxy in
lemma snd_ne_w (a : H.Dart) : a.snd ≠ w := fun h => hw a.fst (h ▸ a.adj.symm)

lemma tgt_adj (z : (subdivideEdge H x y w).Dart) (hz : z.fst ≠ w) :
    H.Adj z.fst (tgt x y w z.fst z.snd) := by
  unfold tgt
  split_ifs with hq hp
  · rw [hp]
    exact hxy
  · have := (adj_w_iff hxy hw).1 (hq ▸ z.adj).symm
    rcases this with h | h
    · exact absurd h hp
    · rw [h]
      exact hxy.symm
  · exact ((adj_ne_w_iff hxy hw hz hq).1 z.adj).1

lemma src_adj (a : H.Dart) : (subdivideEdge H x y w).Adj a.fst (src x y w a.fst a.snd) := by
  unfold src
  split_ifs with he
  · rcases Sym2.eq_iff.1 he with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
    · exact ((adj_w_iff hxy hw).2 (Or.inl rfl)).symm
    · exact ((adj_w_iff hxy hw).2 (Or.inr rfl)).symm
  · exact (adj_ne_w_iff hxy hw (fst_ne_w hw a) (snd_ne_w hw a)).2 ⟨a.adj, he⟩

lemma src_tgt (z : (subdivideEdge H x y w).Dart) (hz : z.fst ≠ w) :
    src x y w z.fst (tgt x y w z.fst z.snd) = z.snd := by
  by_cases hq : z.snd = w
  · have hp := (adj_w_iff hxy hw).1 (hq ▸ z.adj).symm
    unfold tgt src
    rw [ite_eq_left hq, hq]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (by rw [h1]) h2
    · rfl
    · rcases hp with hp | hp
      · exact absurd hp h1
      · exact absurd (by rw [hp]; exact Sym2.eq_swap) h2
  · have hne := ((adj_ne_w_iff hxy hw hz hq).1 z.adj).2
    unfold tgt src
    rw [ite_eq_right hq, ite_eq_right hne]

lemma tgt_src (a : H.Dart) : tgt x y w a.fst (src x y w a.fst a.snd) = a.snd := by
  unfold tgt src
  by_cases he : s(a.fst, a.snd) = s(x, y)
  · rw [ite_eq_left he, ite_eq_left rfl]
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [ite_eq_left h1, h2]
    · rw [ite_eq_right (by rw [h1]; exact hxy.ne.symm), h2]
  · rw [ite_eq_right he, ite_eq_right (snd_ne_w hw a)]

/-- Darts of `H₂` not starting at `w` correspond to darts of `H`:
`(x, w) ↦ (x, y)`, `(y, w) ↦ (y, x)`, with all other darts unchanged. -/
def dartEquiv : {z : (subdivideEdge H x y w).Dart // z.fst ≠ w} ≃ H.Dart where
  toFun z := ⟨(z.1.fst, tgt x y w z.1.fst z.1.snd), tgt_adj hxy hw z.1 z.2⟩
  invFun a := ⟨⟨(a.fst, src x y w a.fst a.snd), src_adj hxy hw a⟩, fst_ne_w hw a⟩
  left_inv z := Subtype.ext (Dart.ext _ _ (Prod.ext rfl (src_tgt hxy hw z.1 z.2)))
  right_inv a := Dart.ext _ _ (Prod.ext rfl (tgt_src hxy hw a))

/-- The dart from `w` to `x`. -/
def dwx : (subdivideEdge H x y w).Dart := ⟨(w, x), (adj_w_iff hxy hw).2 (Or.inl rfl)⟩

/-- The dart from `w` to `y`. -/
def dwy : (subdivideEdge H x y w).Dart := ⟨(w, y), (adj_w_iff hxy hw).2 (Or.inr rfl)⟩

omit [DecidableEq V] in
lemma dwx_ne_dwy : dwx hxy hw ≠ dwy hxy hw := fun h =>
  hxy.ne (congrArg (fun z : (subdivideEdge H x y w).Dart => z.snd) h)

omit [DecidableEq V] in
lemma fst_eq_w_iff (z : (subdivideEdge H x y w).Dart) :
    z.fst = w ↔ z = dwx hxy hw ∨ z = dwy hxy hw := by
  constructor
  · intro h
    have := (adj_w_iff hxy hw).1 (h ▸ z.adj)
    rcases this with h' | h'
    · exact Or.inl (Dart.ext _ _ (Prod.ext h h'))
    · exact Or.inr (Dart.ext _ _ (Prod.ext h h'))
  · rintro (h | h) <;> rw [h] <;> rfl

end Adj

section Rot

variable [Finite V] (hxy : H.Adj x y) (hw : H.IsIsolated w)
  (R₂ : RotationSystem (subdivideEdge H x y w))
include hxy hw

omit [DecidableEq V] [Finite V] hxy hw in
lemma rot_pred (z : (subdivideEdge H x y w).Dart) : (R₂.rot z).fst ≠ w ↔ z.fst ≠ w := by
  rw [R₂.fst_rot]

/-- The induced rotation system on the smoothed graph `H`. -/
def rotH : RotationSystem H where
  rot := (dartEquiv hxy hw).permCongr
    (R₂.rot.subtypePerm (p := fun z => z.fst ≠ w) (rot_pred R₂))
  fst_rot a := R₂.fst_rot _
  sameCycle_rot a a' h := by
    rw [← (dartEquiv hxy hw).apply_symm_apply a, ← (dartEquiv hxy hw).apply_symm_apply a',
      sameCycle_permCongr_iff, sameCycle_subtypePerm]
    exact R₂.sameCycle_rot _ _ h

omit [Finite V] in
lemma rot_dwx : R₂.rot (dwx hxy hw) = dwy hxy hw := by
  have h := (fst_eq_w_iff hxy hw (R₂.rot (dwx hxy hw))).1 (R₂.fst_rot _)
  rcases h with h | h
  · exact absurd h (R₂.rot_ne_self (w := y) ((adj_w_iff hxy hw).2 (Or.inr rfl)) hxy.ne.symm)
  · exact h

omit [Finite V] in
lemma rot_dwy : R₂.rot (dwy hxy hw) = dwx hxy hw := by
  have h := (fst_eq_w_iff hxy hw (R₂.rot (dwy hxy hw))).1 (R₂.fst_rot _)
  rcases h with h | h
  · exact h
  · exact absurd h (R₂.rot_ne_self (w := x) ((adj_w_iff hxy hw).2 (Or.inl rfl)) hxy.ne)

/-- Cut `(w, x)` and `(w, y)` out of the face permutation on all darts of `H₂`. -/
def face₂ : Perm (subdivideEdge H x y w).Dart :=
  cut (cut R₂.facePerm (dwx hxy hw)) (dwy hxy hw)

omit [Finite V] in
lemma face₂_dwx : face₂ hxy hw R₂ (dwx hxy hw) = dwx hxy hw := by
  unfold face₂
  rw [cut_apply_of_ne _ (dwx_ne_dwy hxy hw), cut_apply_self]
  simp [dwx_ne_dwy hxy hw]

omit [Finite V] in
lemma face₂_dwy : face₂ hxy hw R₂ (dwy hxy hw) = dwy hxy hw := cut_apply_self _ _

omit [Finite V] in
lemma face₂_pred (z : (subdivideEdge H x y w).Dart) :
    (face₂ hxy hw R₂ z).fst ≠ w ↔ z.fst ≠ w := by
  rw [not_iff_not, fst_eq_w_iff hxy hw, fst_eq_w_iff hxy hw]
  constructor
  · rintro (h | h)
    · exact Or.inl ((face₂ hxy hw R₂).injective (h.trans (face₂_dwx hxy hw R₂).symm))
    · exact Or.inr ((face₂ hxy hw R₂).injective (h.trans (face₂_dwy hxy hw R₂).symm))
  · rintro (h | h) <;> rw [h]
    · exact Or.inl (face₂_dwx hxy hw R₂)
    · exact Or.inr (face₂_dwy hxy hw R₂)

omit [Finite V] in
/-- The cuts leave a dart unchanged when neither it nor its face successor
starts at `w`. -/
lemma face₂_of_ne (z : (subdivideEdge H x y w).Dart) (h1 : z.fst ≠ w)
    (h2 : (R₂.facePerm z).fst ≠ w) : face₂ hxy hw R₂ z = R₂.facePerm z := by
  have hz1 : z ≠ dwx hxy hw := fun h => h1 (by rw [h]; rfl)
  have hz2 : z ≠ dwy hxy hw := fun h => h1 (by rw [h]; rfl)
  have hf1 : R₂.facePerm z ≠ dwx hxy hw := fun h => h2 (by rw [h]; rfl)
  have hf2 : R₂.facePerm z ≠ dwy hxy hw := fun h => h2 (by rw [h]; rfl)
  unfold face₂
  rw [cut_apply_of_ne _ hz2, cut_apply_of_ne _ hz1, ite_eq_right hf1, ite_eq_right hf2]

omit [Finite V] in
lemma face₂_dwx_symm :
    face₂ hxy hw R₂ (dwx hxy hw).symm = R₂.rot (dwy hxy hw).symm := by
  have hne : (dwx hxy hw).symm ≠ dwx hxy hw := Dart.symm_ne _
  have hne' : (dwx hxy hw).symm ≠ dwy hxy hw := fun h =>
    x_ne_w hxy hw (congrArg (fun z : (subdivideEdge H x y w).Dart => z.fst) h)
  have hφ : R₂.facePerm (dwx hxy hw).symm = dwy hxy hw := by
    rw [RotationSystem.facePerm_apply, Dart.symm_symm, rot_dwx]
  have hφy : R₂.facePerm (dwy hxy hw) ≠ dwx hxy hw := fun h =>
    (w_ne_y hxy hw) (by
      have := congrArg (fun z : (subdivideEdge H x y w).Dart => z.fst) h
      simp only [RotationSystem.facePerm_fst] at this
      exact this.symm)
  unfold face₂
  rw [cut_apply_of_ne _ hne', cut_apply_of_ne _ hne, hφ, ite_eq_right (dwx_ne_dwy hxy hw).symm,
    ite_eq_left rfl, cut_apply_of_ne _ (dwx_ne_dwy hxy hw).symm, ite_eq_right hφy, RotationSystem.facePerm_apply]

omit [Finite V] in
lemma face₂_dwy_symm :
    face₂ hxy hw R₂ (dwy hxy hw).symm = R₂.rot (dwx hxy hw).symm := by
  have hne : (dwy hxy hw).symm ≠ dwx hxy hw := fun h =>
    (w_ne_y hxy hw) (congrArg (fun z : (subdivideEdge H x y w).Dart => z.fst) h).symm
  have hne' : (dwy hxy hw).symm ≠ dwy hxy hw := Dart.symm_ne _
  have hφ : R₂.facePerm (dwy hxy hw).symm = dwx hxy hw := by
    rw [RotationSystem.facePerm_apply, Dart.symm_symm, rot_dwy]
  have hφx : R₂.facePerm (dwx hxy hw) ≠ dwy hxy hw := fun h =>
    (x_ne_w hxy hw) (by
      have := congrArg (fun z : (subdivideEdge H x y w).Dart => z.fst) h
      simp only [RotationSystem.facePerm_fst] at this
      exact this)
  unfold face₂
  rw [cut_apply_of_ne _ hne', cut_apply_of_ne _ hne, ite_eq_left hφ]
  rw [ite_eq_right hφx, RotationSystem.facePerm_apply]

omit [Finite V] in
/-- The dart correspondence intertwines rotation after reversal with the cut face permutation. -/
lemma rot_symm_eq_face₂ (a : H.Dart) :
    R₂.rot ((dartEquiv hxy hw).symm a.symm).1 =
      face₂ hxy hw R₂ ((dartEquiv hxy hw).symm a).1 := by
  by_cases he : s(a.fst, a.snd) = s(x, y)
  · have he' : s(a.snd, a.fst) = s(x, y) := Sym2.eq_swap.trans he
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 : ((dartEquiv hxy hw).symm a).1 = (dwx hxy hw).symm := by
        apply Dart.ext
        show (a.fst, src x y w a.fst a.snd) = (x, w)
        unfold src
        rw [ite_eq_left he, h1]
      have e2 : ((dartEquiv hxy hw).symm a.symm).1 = (dwy hxy hw).symm := by
        apply Dart.ext
        show (a.snd, src x y w a.snd a.fst) = (y, w)
        unfold src
        rw [ite_eq_left he', h2]
      rw [e1, e2, face₂_dwx_symm]
    · have e1 : ((dartEquiv hxy hw).symm a).1 = (dwy hxy hw).symm := by
        apply Dart.ext
        show (a.fst, src x y w a.fst a.snd) = (y, w)
        unfold src
        rw [ite_eq_left he, h1]
      have e2 : ((dartEquiv hxy hw).symm a.symm).1 = (dwx hxy hw).symm := by
        apply Dart.ext
        show (a.snd, src x y w a.snd a.fst) = (x, w)
        unfold src
        rw [ite_eq_left he', h2]
      rw [e1, e2, face₂_dwy_symm]
  · have he' : ¬ s(a.snd, a.fst) = s(x, y) := fun h => he (Sym2.eq_swap.trans h)
    set z := ((dartEquiv hxy hw).symm a).1 with hzdef
    have hz : ((dartEquiv hxy hw).symm a.symm).1 = z.symm := by
      apply Dart.ext
      show (a.snd, src x y w a.snd a.fst) = (src x y w a.fst a.snd, a.fst)
      unfold src
      rw [ite_eq_right he, ite_eq_right he']
    have h2 : (R₂.facePerm z).fst ≠ w := by
      rw [RotationSystem.facePerm_fst]
      show src x y w a.fst a.snd ≠ w
      unfold src
      rw [ite_eq_right he]
      exact snd_ne_w hw a
    rw [hz, face₂_of_ne hxy hw R₂ z (fst_ne_w hw a) h2, RotationSystem.facePerm_apply]

lemma rotH_facePerm :
    (rotH hxy hw R₂).facePerm = (dartEquiv hxy hw).permCongr
      ((face₂ hxy hw R₂).subtypePerm (p := fun z => z.fst ≠ w) (face₂_pred hxy hw R₂)) := by
  ext a : 1
  show (dartEquiv hxy hw) (R₂.rot.subtypePerm (p := fun z => z.fst ≠ w) (rot_pred R₂)
      ((dartEquiv hxy hw).symm a.symm)) =
    (dartEquiv hxy hw) ((face₂ hxy hw R₂).subtypePerm (p := fun z => z.fst ≠ w)
      (face₂_pred hxy hw R₂) ((dartEquiv hxy hw).symm a))
  congr 1
  apply Subtype.ext
  exact rot_symm_eq_face₂ hxy hw R₂ a

/-- Smoothing preserves the number of face-permutation orbits. -/
lemma orbitCount_rotH : orbitCount (rotH hxy hw R₂).facePerm = orbitCount R₂.facePerm := by
  have hfix : ∀ z, ¬ (z.fst ≠ w) → face₂ hxy hw R₂ z = z := by
    intro z hz
    rcases (fst_eq_w_iff hxy hw z).1 (not_not.1 hz) with h | h <;> rw [h]
    · exact face₂_dwx hxy hw R₂
    · exact face₂_dwy hxy hw R₂
  have h1 := orbitCount_eq_subtypePerm_add (face₂ hxy hw R₂) (fun z => z.fst ≠ w)
    (face₂_pred hxy hw R₂) hfix
  have h2 : Nat.card {z : (subdivideEdge H x y w).Dart // ¬ (z.fst ≠ w)} = 2 := by
    have : {z : (subdivideEdge H x y w).Dart | ¬ (z.fst ≠ w)} = {dwx hxy hw, dwy hxy hw} := by
      ext z
      simp only [Set.mem_ofPred_eq, not_not, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact fst_eq_w_iff hxy hw z
    change Nat.card ↥{z : (subdivideEdge H x y w).Dart | ¬ (z.fst ≠ w)} = 2
    rw [Nat.card_coe_set_eq, this, Set.ncard_pair (dwx_ne_dwy hxy hw)]
  have h3 : orbitCount (face₂ hxy hw R₂) = orbitCount (cut R₂.facePerm (dwx hxy hw)) +
      if cut R₂.facePerm (dwx hxy hw) (dwy hxy hw) = dwy hxy hw then 0 else 1 :=
    orbitCount_cut _ _
  have h4 : orbitCount (cut R₂.facePerm (dwx hxy hw)) = orbitCount R₂.facePerm +
      if R₂.facePerm (dwx hxy hw) = dwx hxy hw then 0 else 1 := orbitCount_cut _ _
  have h5 : R₂.facePerm (dwx hxy hw) ≠ dwx hxy hw := R₂.facePerm_ne_self _
  have h6 : cut R₂.facePerm (dwx hxy hw) (dwy hxy hw) ≠ dwy hxy hw := by
    rw [cut_apply_of_ne _ (dwx_ne_dwy hxy hw).symm]
    split_ifs with h
    · intro h'
      have := congrArg (fun z : (subdivideEdge H x y w).Dart => z.fst) h'
      rw [RotationSystem.facePerm_fst] at this
      exact x_ne_w hxy hw this
    · exact R₂.facePerm_ne_self _
  rw [rotH_facePerm, orbitCount_permCongr]
  rw [ite_eq_right h5] at h4
  rw [ite_eq_right h6] at h3
  omega

end Rot

end Smooth

/-- If subdividing an edge through an isolated vertex gives a planar graph, so is the original. -/
theorem IsPlanar.of_subdivideEdge [Finite V] (hxy : H.Adj x y) (hw : H.IsIsolated w)
    (h : IsPlanar (subdivideEdge H x y w)) : IsPlanar H := by
  obtain ⟨R₂, hR₂⟩ := h
  refine ⟨Smooth.rotH hxy hw R₂, ?_⟩
  have hF := Smooth.orbitCount_rotH hxy hw R₂
  have hE := ncard_edgeSet_subdivideEdge hxy hw
  have hI := ncard_isolated_subdivideEdge hxy hw
  have hC := card_connectedComponent_subdivideEdge hxy hw
  unfold RotationSystem.eulerChar RotationSystem.numFaces at hR₂ ⊢
  rw [hF, hI, hC]
  rw [hE] at hR₂
  push_cast at hR₂ ⊢
  omega

end Kuratowski
