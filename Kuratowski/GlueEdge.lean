import Kuratowski.GlueOne
import Kuratowski.PermutationDeletion

/-!
# Gluing planar graphs along a common edge (blueprint `lem:sum2`)

The union of two planar graphs whose supports meet only at the two endpoints of a common edge is
planar.

On the sum of the two dart sets, tagged by origin, we join the rotation cycles twice. This
permutation keeps the common edge twice and contains a bigon. We cut out the two darts of the
common edge of the second graph and transport the remaining darts to darts of the union. The two
transpositions keep the number of face cycles, and deleting the duplicate edge decreases it by one.
We use the deletion formula for general permutations from `PermutationDeletion.lean` and the
isolated-vertex and component counts from `GlueOne.lean`.

The final theorem `IsPlanar.sup_of_inter_eq_edge` requires no decidability instances beyond
finiteness.
-/

namespace Kuratowski.GlueEdge
open SimpleGraph Equiv Equiv.Perm
variable {V : Type*} [DecidableEq V] {G H : SimpleGraph V}

/-- The sum type distinguishing darts of the two graphs by origin. -/
abbrev Darts (G H : SimpleGraph V) := G.Dart ⊕ H.Dart

/-- Forget the origin and read the start vertex of a dart. -/
def vertex : Darts G H → V
  | .inl d => d.fst
  | .inr d => d.fst

/-- Dart reversal within each origin. -/
def reverse : Perm (Darts G H) :=
  Perm.sumCongr (Function.Involutive.toPerm _ Dart.symm_involutive)
    (Function.Involutive.toPerm _ Dart.symm_involutive)

omit [DecidableEq V] in
lemma reverse_involutive : Function.Involutive (reverse (G := G) (H := H)) := by
  intro d
  cases d <;> rfl

/-- Place the two original rotations side by side, by origin. -/
def baseRot (R : RotationSystem G) (S : RotationSystem H) : Perm (Darts G H) :=
  Perm.sumCongr R.rot S.rot

omit [DecidableEq V] in
lemma baseRot_vertex (R : RotationSystem G) (S : RotationSystem H) (d : Darts G H) :
    vertex (baseRot R S d) = vertex d := by
  cases d with
  | inl d => exact R.fst_rot d
  | inr d => exact S.fst_rot d

omit [DecidableEq V] in
lemma invRot_fst (R : RotationSystem G) (d : G.Dart) : (R.rot⁻¹ d).fst = d.fst := by
  simpa using (R.fst_rot (R.rot⁻¹ d)).symm

/-- Join the rotation cycles at the two endpoints of the common edge, choosing a predecessor dart
at each. -/
def joinedRot (R : RotationSystem G) (S : RotationSystem H) (p : G.Dart) (q : H.Dart) :
    Perm (Darts G H) :=
  baseRot R S * swap (.inl p) (.inr (S.rot⁻¹ q)) *
    swap (.inl (R.rot⁻¹ p.symm)) (.inr q.symm)

private lemma vertex_swap {a b : Darts G H} (hab : vertex a = vertex b) (d : Darts G H) :
    vertex (swap a b d) = vertex d := by
  by_cases h : d = a
  · subst d
    rw [swap_apply_left]
    exact hab.symm
  by_cases h' : d = b
  · subst d
    rw [swap_apply_right]
    exact hab
  rw [swap_apply_of_ne_of_ne h h']

lemma joinedRot_vertex (R : RotationSystem G) (S : RotationSystem H) (p : G.Dart) (q : H.Dart)
    (hpq : p.toProd = q.toProd) (d : Darts G H) : vertex (joinedRot R S p q d) = vertex d := by
  have hpa : vertex (.inl p : Darts G H) = vertex (.inr (S.rot⁻¹ q) : Darts G H) := by
    change p.fst = (S.rot⁻¹ q).fst
    rw [invRot_fst]
    exact congrArg Prod.fst hpq
  have hbq : vertex (.inl (R.rot⁻¹ p.symm) : Darts G H) = vertex (.inr q.symm : Darts G H) := by
    change (R.rot⁻¹ p.symm).fst = q.snd
    rw [invRot_fst]
    exact congrArg Prod.snd hpq
  simp only [joinedRot, Perm.mul_apply, baseRot_vertex, vertex_swap hpa, vertex_swap hbq]

lemma joinedRot_left (R : RotationSystem G) (S : RotationSystem H) (p : G.Dart) (q : H.Dart) :
    joinedRot R S p q (.inl p) = .inr q := by
  have hpB : (.inl p : Darts G H) ≠ .inl (R.rot⁻¹ p.symm) := by
    intro h
    have hf := congrArg (fun d : G.Dart ↦ d.fst) (Sum.inl.inj h)
    rw [invRot_fst] at hf
    exact p.adj.ne hf
  rw [joinedRot, Perm.mul_apply, swap_apply_of_ne_of_ne hpB (by simp),
    Perm.mul_apply, swap_apply_left]
  change (Sum.inr (S.rot (S.rot⁻¹ q)) : Darts G H) = .inr q
  simp

lemma joinedRot_right (R : RotationSystem G) (S : RotationSystem H) (p : G.Dart) (q : H.Dart) :
    joinedRot R S p q (.inr q.symm) = .inl p.symm := by
  have hBP : (.inl (R.rot⁻¹ p.symm) : Darts G H) ≠ .inl p := by
    intro h
    have hf := congrArg (fun d : G.Dart ↦ d.fst) (Sum.inl.inj h)
    rw [invRot_fst] at hf
    exact p.adj.ne hf.symm
  rw [joinedRot, Perm.mul_apply, swap_apply_right, Perm.mul_apply,
    swap_apply_of_ne_of_ne hBP (by simp)]
  change (Sum.inl (R.rot (R.rot⁻¹ p.symm)) : Darts G H) = .inl p.symm
  simp

omit [DecidableEq V] in
lemma baseFace (R : RotationSystem G) (S : RotationSystem H) :
    baseRot R S * reverse (G := G) (H := H) = Perm.sumCongr R.facePerm S.facePerm := by
  ext d
  cases d <;> rfl

/-- These two transpositions create a bigon of the first reverse dart and the second forward
dart. -/
lemma joinedFace_bigon (R : RotationSystem G) (S : RotationSystem H) (p : G.Dart) (q : H.Dart) :
    (joinedRot R S p q * reverse (G := G) (H := H)) (.inl p.symm) = .inr q ∧
      (joinedRot R S p q * reverse (G := G) (H := H)) (.inr q) = .inl p.symm := by
  constructor
  · change joinedRot R S p q (.inl p) = .inr q
    exact joinedRot_left R S p q
  · change joinedRot R S p q (.inr q.symm) = .inl p.symm
    exact joinedRot_right R S p q

lemma not_sameCycle_deleted [Finite V] (R : RotationSystem G) (S : RotationSystem H)
    (p : G.Dart) (q : H.Dart) :
    ¬ (joinedRot R S p q * reverse (G := G) (H := H)).SameCycle (.inr q) (.inr q.symm) := by
  obtain ⟨hleft, hright⟩ := joinedFace_bigon R S p q
  apply PermutationDeletion.not_sameCycle_of_two_cycle _ hright hleft
  · exact fun h ↦ Dart.symm_ne q (Sum.inr.inj h)
  · simp

omit [DecidableEq V] in
private lemma baseFace_not_sameCycle [Finite V] (R : RotationSystem G) (S : RotationSystem H)
    (a : G.Dart) (b : H.Dart) :
    ¬ (baseRot R S * reverse (G := G) (H := H)).SameCycle (.inl a) (.inr b) := by
  rw [baseFace]
  exact not_sameCycle_sumCongr_cross R.facePerm S.facePerm a b

/-- The first transposition merges and the second splits, so the total number of face cycles is
preserved. -/
lemma orbitCount_joinedFace [Finite V] (R : RotationSystem G) (S : RotationSystem H)
    (p : G.Dart) (q : H.Dart) :
    orbitCount (joinedRot R S p q * reverse (G := G) (H := H)) =
      orbitCount R.facePerm + orbitCount S.facePerm := by
  have hface : joinedRot R S p q * reverse (G := G) (H := H) =
      (baseRot R S * reverse (G := G) (H := H)) *
        swap (.inl p.symm) (.inr (S.rot⁻¹ q).symm) *
          swap (.inl (R.rot⁻¹ p.symm).symm) (.inr q) :=
    PermutationDeletion.swaps_comp_involution (baseRot R S) reverse reverse_involutive _ _ _ _
  rw [hface]
  let f := baseRot R S * reverse (G := G) (H := H)
  have hc : f.SameCycle (.inl (R.rot⁻¹ p.symm).symm) (.inl p.symm) := by
    have he : f (.inl (R.rot⁻¹ p.symm).symm) = .inl p.symm := by
      change (Sum.inl (R.rot (R.rot⁻¹ p.symm)) : Darts G H) = .inl p.symm
      simp
    rw [← he]
    exact sameCycle_apply_right.2 (.refl _ _)
  have hd : f.SameCycle (.inr q) (.inr (S.rot⁻¹ q).symm) := by
    have he : f (.inr (S.rot⁻¹ q).symm) = .inr q := by
      change (Sum.inr (S.rot (S.rot⁻¹ q)) : Darts G H) = .inr q
      simp
    rw [← he]
    exact sameCycle_apply_left.2 (.refl _ _)
  have hh := PermutationDeletion.orbitCount_two_swaps f (baseFace_not_sameCycle R S _ _) hc hd
    (by simp)
  rw [hh]
  dsimp only [f]
  rw [baseFace, orbitCount_sumCongr]

lemma orbitCount_deletedFace [Finite V] (R : RotationSystem G) (S : RotationSystem H)
    (p : G.Dart) (q : H.Dart) :
    orbitCount ((cut (cut ((joinedRot R S p q * reverse (G := G) (H := H)) *
        swap (.inr q) (.inr q.symm)) (.inr q)) (.inr q.symm)).subtypePerm
      (p := fun x ↦ x ≠ .inr q ∧ x ≠ .inr q.symm)
      (PermutationDeletion.pair_pred _ (PermutationDeletion.cut_pair_left _ (by
        intro h; exact (Dart.symm_ne q).symm (Sum.inr.inj h))) (cut_apply_self _ _))) + 1 =
      orbitCount R.facePerm + orbitCount S.facePerm := by
  have hq : joinedRot R S p q (.inr q) ≠ .inr q := by
    intro h
    have he := (joinedRot R S p q).injective (h.trans (joinedRot_left R S p q).symm)
    cases he
  have hqbar : joinedRot R S p q (.inr q.symm) ≠ .inr q.symm := by
    rw [joinedRot_right]
    simp
  have hqbarq : joinedRot R S p q (.inr q.symm) ≠ .inr q := by
    rw [joinedRot_right]
    simp
  have hh := PermutationDeletion.orbitCount_cut_pair_face (joinedRot R S p q)
    (reverse (G := G) (H := H)) (a := .inr q) (b := .inr q.symm)
    (by intro h; exact (Dart.symm_ne q).symm (Sum.inr.inj h)) rfl rfl hq hqbar hqbarq
    (not_sameCycle_deleted R S p q)
  rw [orbitCount_joinedFace] at hh
  exact hh

/-- The darts other than the two darts of the second copy of the common edge. -/
abbrev Keep (q : H.Dart) :=
  {d : Darts G H // d ≠ .inr q ∧ d ≠ .inr q.symm}

/-- Forget the origin of a remaining dart, giving a dart of the union. -/
def toUnion (q : H.Dart) (d : Keep (G := G) q) : (G ⊔ H).Dart :=
  match d.val with
  | .inl d => ⟨d.toProd, Or.inl d.adj⟩
  | .inr d => ⟨d.toProd, Or.inr d.adj⟩

omit [DecidableEq V] in
lemma toUnion_injective (q : H.Dart)
    (hshare : ∀ d : H.Dart, G.Adj d.fst d.snd → d = q ∨ d = q.symm) :
    Function.Injective (toUnion (G := G) q) := by
  intro d e h
  have hp := congrArg Dart.toProd h
  apply Subtype.ext
  rcases d with ⟨a, ha⟩
  rcases e with ⟨b, hb⟩
  rcases a with a | a <;> rcases b with b | b
  · change a.toProd = b.toProd at hp
    exact congrArg Sum.inl (Dart.ext _ _ hp)
  · change a.toProd = b.toProd at hp
    have hG : G.Adj b.fst b.snd := by
      rw [← hp]
      exact a.adj
    rcases hshare b hG with h | h
    · exact False.elim (hb.1 (congrArg Sum.inr h))
    · exact False.elim (hb.2 (congrArg Sum.inr h))
  · change a.toProd = b.toProd at hp
    have hG : G.Adj a.fst a.snd := by
      rw [hp]
      exact b.adj
    rcases hshare a hG with h | h
    · exact False.elim (ha.1 (congrArg Sum.inr h))
    · exact False.elim (ha.2 (congrArg Sum.inr h))
  · change a.toProd = b.toProd at hp
    exact congrArg Sum.inr (Dart.ext _ _ hp)

omit [DecidableEq V] in
lemma toUnion_surjective (q : H.Dart) (hq : G.Adj q.fst q.snd) :
    Function.Surjective (toUnion (G := G) q) := by
  intro d
  by_cases hG : G.Adj d.fst d.snd
  · exact ⟨⟨.inl ⟨d.toProd, hG⟩, by simp⟩, rfl⟩
  · have hH : H.Adj d.fst d.snd := d.adj.resolve_left hG
    let b : H.Dart := ⟨d.toProd, hH⟩
    have hb : (.inr b : Darts G H) ≠ .inr q ∧ (.inr b : Darts G H) ≠ .inr q.symm := by
      constructor
      · intro h
        have hp := congrArg Dart.toProd (Sum.inr.inj h)
        apply hG
        change G.Adj b.toProd.1 b.toProd.2
        rw [hp]
        exact hq
      · intro h
        have hp := congrArg Dart.toProd (Sum.inr.inj h)
        apply hG
        change G.Adj b.toProd.1 b.toProd.2
        rw [hp]
        exact hq.symm
    exact ⟨⟨.inr b, hb⟩, rfl⟩

/-- If the only shared darts are the two orientations of the common edge, the remaining darts
are in bijection with the darts of the union. -/
noncomputable def dartEquiv (q : H.Dart) (hq : G.Adj q.fst q.snd)
    (hshare : ∀ d : H.Dart, G.Adj d.fst d.snd → d = q ∨ d = q.symm) :
    Keep (G := G) q ≃ (G ⊔ H).Dart :=
  Equiv.ofBijective (toUnion q) ⟨toUnion_injective q hshare, toUnion_surjective q hq⟩

omit [DecidableEq V] in
lemma vertex_eq_of_sameCycle [Finite V] {f : Perm (Darts G H)}
    (hf : ∀ d, vertex (f d) = vertex d) {d e : Darts G H} (h : f.SameCycle d e) :
    vertex d = vertex e := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  have hp : ∀ n : ℕ, vertex ((f ^ n) d) = vertex d := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simpa only [pow_succ', Perm.mul_apply, hf] using ih
  exact (hp n).symm

lemma joinedRot_sameCycle [Finite V] (R : RotationSystem G) (S : RotationSystem H)
    (p : G.Dart) (q : H.Dart) (hpq : p.toProd = q.toProd)
    (hshare : ∀ (a : G.Dart) (b : H.Dart), a.fst = b.fst → a.fst = p.fst ∨ a.fst = p.snd)
    (d e : Darts G H) (hde : vertex d = vertex e) :
    (joinedRot R S p q).SameCycle d e := by
  let f := baseRot R S
  let P : Darts G H := .inl p
  let A : Darts G H := .inr (S.rot⁻¹ q)
  let B : Darts G H := .inl (R.rot⁻¹ p.symm)
  let Q : Darts G H := .inr q.symm
  have hX : ¬ f.SameCycle P A := not_sameCycle_sumCongr_cross R.rot S.rot _ _
  have hxjoin := sameCycle_mul_swap_of_not hX
  have keepX {a b : Darts G H} (h : f.SameCycle a b) :
      (f * swap P A).SameCycle a b := hxjoin.mul_swap_of_sameCycle h
  have hnBP : ¬ f.SameCycle B P := by
    intro h
    have hv := vertex_eq_of_sameCycle (baseRot_vertex R S) h
    change (R.rot⁻¹ p.symm).fst = p.fst at hv
    rw [invRot_fst] at hv
    exact p.adj.ne hv.symm
  have hnBA : ¬ f.SameCycle B A := by
    intro h
    have hv := vertex_eq_of_sameCycle (baseRot_vertex R S) h
    change (R.rot⁻¹ p.symm).fst = (S.rot⁻¹ q).fst at hv
    rw [invRot_fst, invRot_fst] at hv
    exact p.adj.ne ((congrArg Prod.fst hpq).trans hv.symm)
  have hY : ¬ (f * swap P A).SameCycle B Q := by
    intro h
    rcases (sameCycle_iff_of_mul_swap_not hX).1 h with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact not_sameCycle_sumCongr_cross R.rot S.rot _ _ h
    · exact hnBP h
    · exact hnBA h
  have hyjoin := sameCycle_mul_swap_of_not hY
  have keepY {a b : Darts G H} (h : (f * swap P A).SameCycle a b) :
      (f * swap P A * swap B Q).SameCycle a b := hyjoin.mul_swap_of_sameCycle h
  have left {a b : G.Dart} (h : R.rot.SameCycle a b) :
      f.SameCycle (.inl a) (.inl b) := sameCycle_sumCongr_left _ _ h
  have right {a b : H.Dart} (h : S.rot.SameCycle a b) :
      f.SameCycle (.inr a) (.inr b) := sameCycle_sumCongr_right _ _ h
  have cross (a : G.Dart) (b : H.Dart) (he : a.fst = b.fst) :
      (joinedRot R S p q).SameCycle (.inl a) (.inr b) := by
    change (f * swap P A * swap B Q).SameCycle _ _
    rcases hshare a b he with hx | hy
    · have hb : b.fst = (S.rot⁻¹ q).fst :=
        he.symm.trans (hx.trans ((congrArg Prod.fst hpq).trans (invRot_fst S q).symm))
      exact keepY ((keepX (left (R.sameCycle_rot a p hx))).trans
        (hxjoin.trans (keepX (right (S.sameCycle_rot b _ hb))).symm))
    · have ha : a.fst = (R.rot⁻¹ p.symm).fst := hy.trans (invRot_fst R p.symm).symm
      have hb : b.fst = q.symm.fst := he.symm.trans (hy.trans (congrArg Prod.snd hpq))
      exact (keepY (keepX (left (R.sameCycle_rot a _ ha)))).trans
        (hyjoin.trans (keepY (keepX (right (S.sameCycle_rot b _ hb)))).symm)
  rcases d with d | d <;> rcases e with e | e
  · exact keepY (keepX (left (R.sameCycle_rot d e hde)))
  · exact cross d e hde
  · exact (cross e d hde.symm).symm
  · exact keepY (keepX (right (S.sameCycle_rot d e hde)))

omit [DecidableEq V] in
lemma reverse_pred (q : H.Dart) (d : Darts G H) :
    (reverse (G := G) (H := H) d ≠ .inr q ∧ reverse d ≠ .inr q.symm) ↔
      (d ≠ .inr q ∧ d ≠ .inr q.symm) := by
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · intro h
      subst d
      exact hb rfl
    · intro h
      subst d
      exact ha rfl
  · rintro ⟨ha, hb⟩
    exact ⟨fun h ↦ hb (reverse.injective h), fun h ↦ ha (reverse.injective h)⟩

def reverseKeep (q : H.Dart) : Perm (Keep (G := G) q) :=
  (reverse (G := G) (H := H)).subtypePerm (reverse_pred q)

omit [DecidableEq V] in
lemma dartEquiv_vertex (q : H.Dart) (hq : G.Adj q.fst q.snd)
    (hshare : ∀ d : H.Dart, G.Adj d.fst d.snd → d = q ∨ d = q.symm)
    (d : Keep (G := G) q) : (dartEquiv q hq hshare d).fst = vertex d.val := by
  rcases d with ⟨d, hd⟩
  cases d <;> rfl

omit [DecidableEq V] in
lemma dartEquiv_reverse (q : H.Dart) (hq : G.Adj q.fst q.snd)
    (hshare : ∀ d : H.Dart, G.Adj d.fst d.snd → d = q ∨ d = q.symm)
    (d : Keep (G := G) q) : dartEquiv q hq hshare (reverseKeep q d) =
      (dartEquiv q hq hshare d).symm := by
  apply Dart.ext
  rcases d with ⟨d, hd⟩
  cases d <;> rfl

/-- Cut the two darts of the duplicate edge out of the rotation cycles, making them fixed points. -/
def cutRot (R : RotationSystem G) (S : RotationSystem H) (p : G.Dart) (q : H.Dart) :
    Perm (Darts G H) := cut (cut (joinedRot R S p q) (.inr q)) (.inr q.symm)

lemma cutRot_pred (R : RotationSystem G) (S : RotationSystem H) (p : G.Dart) (q : H.Dart)
    (d : Darts G H) : (cutRot R S p q d ≠ .inr q ∧ cutRot R S p q d ≠ .inr q.symm) ↔
      (d ≠ .inr q ∧ d ≠ .inr q.symm) :=
  PermutationDeletion.pair_pred _ (PermutationDeletion.cut_pair_left _
    (by intro h; exact (Dart.symm_ne q).symm (Sum.inr.inj h))) (cut_apply_self _ _) d

/-- The rotation on the subtype without the two fixed points. -/
def deletedRot (R : RotationSystem G) (S : RotationSystem H) (p : G.Dart) (q : H.Dart) :
    Perm (Keep (G := G) q) := (cutRot R S p q).subtypePerm (cutRot_pred R S p q)

lemma cutRot_vertex (R : RotationSystem G) (S : RotationSystem H) (p : G.Dart) (q : H.Dart)
    (hpq : p.toProd = q.toProd) (d : Darts G H) : vertex (cutRot R S p q d) = vertex d := by
  have h₁ : ∀ x : Darts G H,
      vertex (cut (joinedRot R S p q) (.inr q) x) = vertex x :=
    cut_preserves (joinedRot R S p q) (.inr q) vertex (joinedRot_vertex R S p q hpq)
  exact cut_preserves (cut (joinedRot R S p q) (.inr q)) (.inr q.symm) vertex h₁ d

/-- Build the rotation system of the union by joining the rotations at the two endpoints and
deleting the duplicate edge. -/
noncomputable def rotation [Finite V] (R : RotationSystem G) (S : RotationSystem H)
    (p : G.Dart) (q : H.Dart) (hpq : p.toProd = q.toProd) (hq : G.Adj q.fst q.snd)
    (hvertices : ∀ (a : G.Dart) (b : H.Dart), a.fst = b.fst → a.fst = p.fst ∨ a.fst = p.snd)
    (hshare : ∀ d : H.Dart, G.Adj d.fst d.snd → d = q ∨ d = q.symm) :
    RotationSystem (G ⊔ H) := by
  let E := dartEquiv q hq hshare
  refine { rot := E.permCongr (deletedRot R S p q), fst_rot := ?_, sameCycle_rot := ?_ }
  · intro d
    obtain ⟨d, rfl⟩ := E.surjective d
    rw [Equiv.permCongr_apply, E.symm_apply_apply]
    change (dartEquiv q hq hshare (deletedRot R S p q d)).fst =
      (dartEquiv q hq hshare d).fst
    rw [dartEquiv_vertex, dartEquiv_vertex]
    exact cutRot_vertex R S p q hpq d.val
  · intro d e h
    obtain ⟨d, rfl⟩ := E.surjective d
    obtain ⟨e, rfl⟩ := E.surjective e
    apply (sameCycle_permCongr_iff E _ d e).2
    apply sameCycle_subtypePerm.2
    apply sameCycle_cut d.property.2 e.property.2
    apply sameCycle_cut d.property.1 e.property.1
    apply joinedRot_sameCycle R S p q hpq hvertices d.val e.val
    change (dartEquiv q hq hshare d).fst = (dartEquiv q hq hshare e).fst at h
    simpa only [dartEquiv_vertex] using h

/-- The permutation of all darts obtained by multiplying the face permutation by the
transpositions and cutting out the two points to be deleted. -/
def cutFace (R : RotationSystem G) (S : RotationSystem H) (p : G.Dart) (q : H.Dart) :
    Perm (Darts G H) := cut (cut ((joinedRot R S p q * reverse (G := G) (H := H)) *
      swap (.inr q) (.inr q.symm)) (.inr q)) (.inr q.symm)

lemma cutFace_pred (R : RotationSystem G) (S : RotationSystem H) (p : G.Dart) (q : H.Dart)
    (d : Darts G H) : (cutFace R S p q d ≠ .inr q ∧ cutFace R S p q d ≠ .inr q.symm) ↔
      (d ≠ .inr q ∧ d ≠ .inr q.symm) :=
  PermutationDeletion.pair_pred _ (PermutationDeletion.cut_pair_left _
    (by intro h; exact (Dart.symm_ne q).symm (Sum.inr.inj h))) (cut_apply_self _ _) d

/-- The face permutation without the two fixed points. -/
def deletedFace (R : RotationSystem G) (S : RotationSystem H) (p : G.Dart) (q : H.Dart) :
    Perm (Keep (G := G) q) := (cutFace R S p q).subtypePerm (cutFace_pred R S p q)

lemma rotation_facePerm [Finite V] (R : RotationSystem G) (S : RotationSystem H)
    (p : G.Dart) (q : H.Dart) (hpq : p.toProd = q.toProd) (hq : G.Adj q.fst q.snd)
    (hvertices : ∀ (a : G.Dart) (b : H.Dart), a.fst = b.fst → a.fst = p.fst ∨ a.fst = p.snd)
    (hshare : ∀ d : H.Dart, G.Adj d.fst d.snd → d = q ∨ d = q.symm) :
    (rotation R S p q hpq hq hvertices hshare).facePerm =
      (dartEquiv q hq hshare).permCongr (deletedFace R S p q) := by
  let E := dartEquiv q hq hshare
  ext1 d
  obtain ⟨d, rfl⟩ := E.surjective d
  rw [RotationSystem.facePerm_apply]
  have hs : (E d).symm = E (reverseKeep q d) := (dartEquiv_reverse q hq hshare d).symm
  rw [hs]
  change E.permCongr (deletedRot R S p q) (E (reverseKeep q d)) =
    E.permCongr (deletedFace R S p q) (E d)
  rw [Equiv.permCongr_apply, Equiv.permCongr_apply,
    E.symm_apply_apply, E.symm_apply_apply]
  apply congrArg E
  apply Subtype.ext
  exact PermutationDeletion.cut_pair_comp (joinedRot R S p q)
    (reverse (G := G) (H := H)) reverse_involutive
    (by intro h; exact (Dart.symm_ne q).symm (Sum.inr.inj h)) rfl rfl d.property.1 d.property.2

lemma orbitCount_rotation_facePerm [Finite V] (R : RotationSystem G) (S : RotationSystem H)
    (p : G.Dart) (q : H.Dart) (hpq : p.toProd = q.toProd) (hq : G.Adj q.fst q.snd)
    (hvertices : ∀ (a : G.Dart) (b : H.Dart), a.fst = b.fst → a.fst = p.fst ∨ a.fst = p.snd)
    (hshare : ∀ d : H.Dart, G.Adj d.fst d.snd → d = q ∨ d = q.symm) :
    orbitCount (rotation R S p q hpq hq hvertices hshare).facePerm + 1 =
      orbitCount R.facePerm + orbitCount S.facePerm := by
  rw [rotation_facePerm, orbitCount_permCongr]
  exact orbitCount_deletedFace R S p q

omit [DecidableEq V] in
lemma ncard_edgeSet_sup [Finite V] (q : H.Dart) (hq : G.Adj q.fst q.snd)
    (hshare : ∀ d : H.Dart, G.Adj d.fst d.snd → d = q ∨ d = q.symm) :
    (G ⊔ H).edgeSet.ncard + 1 = G.edgeSet.ncard + H.edgeSet.ncard := by
  have hc := Set.ncard_add_ncard_compl ({.inr q, .inr q.symm} : Set (Darts G H))
  have heq : ({.inr q, .inr q.symm} : Set (Darts G H))ᶜ =
      {d | d ≠ .inr q ∧ d ≠ .inr q.symm} := by
    ext d
    simp
  rw [Set.ncard_pair (by intro h; exact (Dart.symm_ne q).symm (Sum.inr.inj h)), heq] at hc
  change 2 + Nat.card (Keep (G := G) q) = Nat.card (G.Dart ⊕ H.Dart) at hc
  rw [Nat.card_congr (dartEquiv q hq hshare), Nat.card_sum,
    card_dart_eq, card_dart_eq, card_dart_eq] at hc
  omega

end Kuratowski.GlueEdge

namespace Kuratowski
open SimpleGraph
variable {V : Type*} {G H : SimpleGraph V}

/-- The union of two planar graphs whose supports meet only at the two endpoints of a common edge
is planar. -/
theorem IsPlanar.sup_of_inter_eq_edge [Finite V] {x y : V} (hG : IsPlanar G) (hH : IsPlanar H)
    (hGxy : G.Adj x y) (hHxy : H.Adj x y) (hs : G.support ∩ H.support = {x, y}) :
    IsPlanar (G ⊔ H) := by
  classical
  obtain ⟨R, hR⟩ := hG
  obtain ⟨S, hS⟩ := hH
  let p : G.Dart := ⟨(x,y), hGxy⟩
  let q : H.Dart := ⟨(x,y), hHxy⟩
  have hvertices : ∀ (a : G.Dart) (b : H.Dart), a.fst = b.fst →
      a.fst = p.fst ∨ a.fst = p.snd := by
    intro a b hab
    have ha : a.fst ∈ G.support ∩ H.support :=
      ⟨a.adj.mem_support_left, by rw [hab]; exact b.adj.mem_support_left⟩
    change a.fst = x ∨ a.fst = y
    simpa only [hs, Set.mem_insert_iff, Set.mem_singleton_iff] using ha
  have hshare : ∀ d : H.Dart, G.Adj d.fst d.snd → d = q ∨ d = q.symm := by
    intro d hd
    have h1 := hvertices ⟨d.toProd, hd⟩ d rfl
    have h2 := hvertices ⟨d.toProd.swap, hd.symm⟩ d.symm rfl
    change d.fst = x ∨ d.fst = y at h1
    change d.snd = x ∨ d.snd = y at h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact False.elim (d.adj.ne (h1.trans h2.symm))
    · exact Or.inl (Dart.ext _ _ (Prod.ext h1 h2))
    · exact Or.inr (Dart.ext _ _ (Prod.ext h1 h2))
    · exact False.elim (d.adj.ne (h1.trans h2.symm))
  let T := GlueEdge.rotation R S p q rfl hGxy hvertices hshare
  refine ⟨T, ?_⟩
  have hO : orbitCount T.facePerm + 1 = orbitCount R.facePerm + orbitCount S.facePerm :=
    GlueEdge.orbitCount_rotation_facePerm R S p q rfl hGxy hvertices hshare
  have hE := GlueEdge.ncard_edgeSet_sup q hGxy hshare
  have hI := ncard_isolated_sup_add (G := G) (H := H)
  rw [hs, Set.ncard_pair hGxy.ne] at hI
  have hC := card_connectedComponent_sup_of_inter_eq_edge hGxy hHxy hs
  have hO' := congrArg (fun n : ℕ ↦ (n : ℤ)) hO
  have hE' := congrArg (fun n : ℕ ↦ (n : ℤ)) hE
  have hI' := congrArg (fun n : ℕ ↦ (n : ℤ)) hI
  have hC' := congrArg (fun n : ℕ ↦ (n : ℤ)) hC
  unfold RotationSystem.eulerChar RotationSystem.numFaces at hR hS ⊢
  push_cast at hR hS hO' hE' hI' hC' ⊢
  omega

end Kuratowski
