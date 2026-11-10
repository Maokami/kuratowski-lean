import Kuratowski.Connected
import Kuratowski.Euler

/-!
# Splitting a vertex (blueprint `lem:split2`)

Split a vertex `w` in two by attaching a set `B` of its darts to a new vertex `none`. The vertex
type is `Option V`, with the vertices of `V` embedded by `some`. The new start vertex of a dart `d`
is `none` if `d ∈ B` and `some d.fst` otherwise (`splitFst`); the new end vertex is the new start
vertex of the reversed dart.

* `splitGraph`: the graph whose edges are the endpoint pairs of the new darts. It has no loops if
  `B` contains only darts at one vertex.
* `splitDartEquiv`: the bijection between old and new darts. It commutes with reversal
  (`splitDartEquiv_symm`).
-/

namespace Kuratowski

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

open Classical in
/-- The new start vertex of a dart: the new vertex `none` if it lies in `B`, otherwise the
original start vertex. -/
noncomputable def splitFst (B : Set G.Dart) (d : G.Dart) : Option V :=
  if d ∈ B then none else some d.fst

theorem splitFst_of_mem {B : Set G.Dart} {d : G.Dart} (h : d ∈ B) : splitFst B d = none := by
  simp [splitFst, h]

theorem splitFst_of_not_mem {B : Set G.Dart} {d : G.Dart} (h : d ∉ B) :
    splitFst B d = some d.fst := by
  simp [splitFst, h]

theorem splitFst_eq_none_iff {B : Set G.Dart} {d : G.Dart} : splitFst B d = none ↔ d ∈ B := by
  by_cases h : d ∈ B
  · simp [splitFst_of_mem h, h]
  · simp [splitFst_of_not_mem h, h]

variable {w : V} {B : Set G.Dart}

/-- If `B` contains only darts at `w`, a dart and its reversal cannot both lie in `B`. -/
theorem symm_not_mem_of_fst (hB : ∀ d ∈ B, d.fst = w) {d : G.Dart} (hd : d ∈ B) :
    d.symm ∉ B := by
  intro h
  have h1 := hB d hd
  have h2 := hB d.symm h
  exact d.adj.ne (h1.trans h2.symm)

theorem splitFst_ne_splitFst_symm (hB : ∀ d ∈ B, d.fst = w) (d : G.Dart) :
    splitFst B d ≠ splitFst B d.symm := by
  by_cases h : d ∈ B
  · rw [splitFst_of_mem h, splitFst_of_not_mem (symm_not_mem_of_fst hB h)]
    exact (Option.some_ne_none _).symm
  · by_cases h' : d.symm ∈ B
    · rw [splitFst_of_not_mem h, splitFst_of_mem h']
      exact Option.some_ne_none _
    · rw [splitFst_of_not_mem h, splitFst_of_not_mem h']
      exact fun e ↦ d.adj.ne (Option.some.inj e)

/-- The graph with `w` split (on `Option V`). -/
def splitGraph (B : Set G.Dart) (hB : ∀ d ∈ B, d.fst = w) : SimpleGraph (Option V) where
  Adj x y := ∃ d : G.Dart, splitFst B d = x ∧ splitFst B d.symm = y
  symm := ⟨fun x y ⟨d, h1, h2⟩ ↦ ⟨d.symm, h2, by rwa [Dart.symm_symm]⟩⟩
  loopless := ⟨fun x ⟨d, h1, h2⟩ ↦ splitFst_ne_splitFst_symm hB d (h1.trans h2.symm)⟩

variable (hB : ∀ d ∈ B, d.fst = w)

theorem splitGraph_adj {x y : Option V} :
    (splitGraph B hB).Adj x y ↔ ∃ d : G.Dart, splitFst B d = x ∧ splitFst B d.symm = y :=
  Iff.rfl

/-- Transport an original dart to a dart of the split graph. -/
noncomputable def splitDart (d : G.Dart) : (splitGraph B hB).Dart :=
  ⟨(splitFst B d, splitFst B d.symm), ⟨d, rfl, rfl⟩⟩

@[simp] theorem splitDart_toProd (d : G.Dart) :
    (splitDart hB d).toProd = (splitFst B d, splitFst B d.symm) := rfl

theorem splitDart_injective : Function.Injective (splitDart hB) := by
  intro d e h
  have h1 : splitFst B d = splitFst B e := congrArg (fun x ↦ x.toProd.1) h
  have h2 : splitFst B d.symm = splitFst B e.symm := congrArg (fun x ↦ x.toProd.2) h
  -- start vertices: both `w` if in `B`, otherwise the values under `some`
  have hfst : d.fst = e.fst := by
    by_cases hd : d ∈ B
    · have he : e ∈ B := splitFst_eq_none_iff.1 (h1.symm.trans (splitFst_of_mem hd))
      exact (hB d hd).trans (hB e he).symm
    · have he : e ∉ B := fun he ↦ hd (splitFst_eq_none_iff.1 (h1.trans (splitFst_of_mem he)))
      rw [splitFst_of_not_mem hd, splitFst_of_not_mem he] at h1
      exact Option.some.inj h1
  have hsnd : d.snd = e.snd := by
    by_cases hd : d.symm ∈ B
    · have he : e.symm ∈ B := splitFst_eq_none_iff.1 (h2.symm.trans (splitFst_of_mem hd))
      exact (hB _ hd).trans (hB _ he).symm
    · have he : e.symm ∉ B := fun he ↦
        hd (splitFst_eq_none_iff.1 (h2.trans (splitFst_of_mem he)))
      rw [splitFst_of_not_mem hd, splitFst_of_not_mem he] at h2
      exact Option.some.inj h2
  exact Dart.ext _ _ (Prod.ext hfst hsnd)

theorem splitDart_surjective : Function.Surjective (splitDart hB) := by
  intro x
  obtain ⟨d, h1, h2⟩ := x.adj
  exact ⟨d, Dart.ext _ _ (Prod.ext h1 h2)⟩

/-- The bijection between the original darts and the darts of the split graph. -/
noncomputable def splitDartEquiv : G.Dart ≃ (splitGraph B hB).Dart :=
  Equiv.ofBijective (splitDart hB) ⟨splitDart_injective hB, splitDart_surjective hB⟩

@[simp] theorem splitDartEquiv_apply (d : G.Dart) : splitDartEquiv hB d = splitDart hB d := rfl

/-- The dart bijection commutes with reversal. -/
theorem splitDartEquiv_symm (d : G.Dart) :
    splitDartEquiv hB d.symm = (splitDartEquiv hB d).symm := by
  apply Dart.ext
  simp [Dart.symm_symm]

/-! ### The split rotation system -/

namespace RotationSystem

open Equiv Equiv.Perm

variable [DecidableEq V] (R : RotationSystem G)

/-- The rotation after splitting (on the original darts): `ρ' = ρ · (ē₁ ē₂)`. -/
def splitRot (e₁ e₂ : G.Dart) : Perm G.Dart := R.rot * swap e₁.symm e₂.symm

/-- The `ρ'`-cycle of `ē₂`: the darts attached to the new vertex `none`. -/
def splitSet (e₁ e₂ : G.Dart) : Set G.Dart := {d | (R.splitRot e₁ e₂).SameCycle e₂.symm d}

variable {R} {e₁ e₂ : G.Dart}

theorem splitRot_fst (he : e₁.snd = e₂.snd) (d : G.Dart) :
    (R.splitRot e₁ e₂ d).fst = d.fst := by
  unfold splitRot
  rw [Perm.mul_apply, R.fst_rot]
  by_cases h1 : d = e₁.symm
  · subst h1
    rw [swap_apply_left]
    exact he.symm
  · by_cases h2 : d = e₂.symm
    · subst h2
      rw [swap_apply_right]
      exact he
    · rw [swap_apply_of_ne_of_ne h1 h2]

omit [DecidableEq V] in
/-- Two points in one cycle of a permutation preserving start vertices have the same start
vertex. -/
theorem fst_eq_of_sameCycle [Finite V] {f : Perm G.Dart} (hf : ∀ d, (f d).fst = d.fst)
    {x y : G.Dart} (h : f.SameCycle x y) : x.fst = y.fst := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn]
  clear hn h
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, hf, ih]

theorem splitSet_fst [Finite V] (he : e₁.snd = e₂.snd) :
    ∀ d ∈ R.splitSet e₁ e₂, d.fst = e₂.snd := fun _ hd ↦
  (fst_eq_of_sameCycle (splitRot_fst he) hd).symm

variable [Finite V]

/-- The rotation system obtained by splitting a vertex at two darts entering it. -/
noncomputable def split (R : RotationSystem G) (he : e₁.snd = e₂.snd) :
    RotationSystem (splitGraph (R.splitSet e₁ e₂) (splitSet_fst he)) where
  rot := (splitDartEquiv (splitSet_fst he)).permCongr (R.splitRot e₁ e₂)
  fst_rot x := by
    obtain ⟨d, rfl⟩ := (splitDartEquiv (splitSet_fst he)).surjective x
    rw [permCongr_apply, Equiv.symm_apply_apply]
    change splitFst _ (R.splitRot e₁ e₂ d) = splitFst _ d
    have hmem : R.splitRot e₁ e₂ d ∈ R.splitSet e₁ e₂ ↔ d ∈ R.splitSet e₁ e₂ :=
      sameCycle_apply_right
    by_cases hd : d ∈ R.splitSet e₁ e₂
    · rw [splitFst_of_mem hd, splitFst_of_mem (hmem.2 hd)]
    · rw [splitFst_of_not_mem hd, splitFst_of_not_mem (fun h ↦ hd (hmem.1 h)),
        splitRot_fst he]
  sameCycle_rot x y hxy := by
    obtain ⟨d, rfl⟩ := (splitDartEquiv (splitSet_fst he)).surjective x
    obtain ⟨d', rfl⟩ := (splitDartEquiv (splitSet_fst he)).surjective y
    rw [sameCycle_permCongr_iff]
    change splitFst _ d = splitFst _ d' at hxy
    by_cases hd : d ∈ R.splitSet e₁ e₂
    · have hd' : d' ∈ R.splitSet e₁ e₂ :=
        splitFst_eq_none_iff.1 (hxy.symm.trans (splitFst_of_mem hd))
      exact (show (R.splitRot e₁ e₂).SameCycle e₂.symm d from hd).symm.trans hd'
    · have hd' : d' ∉ R.splitSet e₁ e₂ := fun h ↦
        hd (splitFst_eq_none_iff.1 (hxy.trans (splitFst_of_mem h)))
      rw [splitFst_of_not_mem hd, splitFst_of_not_mem hd'] at hxy
      have hρ := R.sameCycle_rot d d' (Option.some.inj hxy)
      have hρ' : R.rot = R.splitRot e₁ e₂ * swap e₁.symm e₂.symm := by
        rw [splitRot, mul_swap_mul_self]
      rw [hρ'] at hρ
      rcases sameCycle_mul_swap_zone hρ with h | ⟨h1 | h1, h2 | h2⟩
      · exact h
      · exact h1.trans h2.symm
      · exact absurd h2.symm hd'
      · exact absurd h1.symm hd
      · exact absurd h1.symm hd

/-- The face permutation of the split rotation system is the transport of `φ · (e₁ e₂)`. -/
theorem split_facePerm (R : RotationSystem G) (he : e₁.snd = e₂.snd) :
    (R.split he).facePerm =
      (splitDartEquiv (splitSet_fst he)).permCongr (R.facePerm * swap e₁ e₂) := by
  ext1 x
  obtain ⟨d, rfl⟩ := (splitDartEquiv (splitSet_fst he)).surjective x
  rw [facePerm_apply, ← splitDartEquiv_symm,
    show (R.split he).rot = (splitDartEquiv (splitSet_fst he)).permCongr (R.splitRot e₁ e₂)
      from rfl, permCongr_apply, permCongr_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  congr 1
  rw [splitRot, Perm.mul_apply, Perm.mul_apply, facePerm_apply]
  congr 1
  exact (Dart.symm_involutive.injective.map_swap e₁ e₂ d).symm

omit [Finite V] in
/-- `ē₂` is on the `none` side and `ē₁` on the `some w` side. Both lie in one `ρ`-cycle at `w`,
so the transposition splits that cycle. -/
theorem symm_mem_splitSet : e₂.symm ∈ R.splitSet e₁ e₂ := SameCycle.refl _ _

theorem symm_not_mem_splitSet (he : e₁.snd = e₂.snd) (hne : e₁ ≠ e₂) :
    e₁.symm ∉ R.splitSet e₁ e₂ := by
  intro h
  have hne' : e₁.symm ≠ e₂.symm := fun e ↦ hne (Dart.symm_involutive.injective e)
  exact not_sameCycle_mul_swap_of_sameCycle hne' (R.sameCycle_rot _ _ he) h.symm

/-- Splitting at two corners of the same face adds one face cycle. -/
theorem orbitCount_split_facePerm (he : e₁.snd = e₂.snd) (hne : e₁ ≠ e₂)
    (hface : R.facePerm.SameCycle e₁ e₂) :
    orbitCount (R.split he).facePerm = orbitCount R.facePerm + 1 := by
  rw [split_facePerm, orbitCount_permCongr, orbitCount_mul_swap_of_sameCycle hne hface]

/-- The dart bijection shows that the number of edges is unchanged. -/
theorem ncard_edgeSet_splitGraph (he : e₁.snd = e₂.snd) :
    (splitGraph (R.splitSet e₁ e₂) (splitSet_fst he)).edgeSet.ncard = G.edgeSet.ncard := by
  have h1 := card_dart_eq (splitGraph (R.splitSet e₁ e₂) (splitSet_fst he))
  have h2 := card_dart_eq G
  have h3 := Nat.card_congr (splitDartEquiv (splitSet_fst (R := R) he))
  omega

/-- The isolated vertices are the original isolated vertices under `some`. The two halves of `w`,
`some w` and `none`, are not isolated. -/
theorem isolated_splitGraph (he : e₁.snd = e₂.snd) (hne : e₁ ≠ e₂) :
    {x | (splitGraph (R.splitSet e₁ e₂) (splitSet_fst he)).IsIsolated x} =
      Option.some '' {v | G.IsIsolated v} := by
  ext x
  rcases x with _ | u
  · simp only [Set.mem_ofPred_eq, Set.mem_image, reduceCtorEq, and_false, exists_false,
      iff_false]
    intro hiso
    exact hiso _ ⟨e₂.symm, splitFst_of_mem symm_mem_splitSet, rfl⟩
  · simp only [Set.mem_ofPred_eq, Set.mem_image, Option.some.injEq, exists_eq_right]
    constructor
    · intro hiso x hux
      let d : G.Dart := ⟨(u, x), hux⟩
      by_cases hd : d ∈ R.splitSet e₁ e₂
      · have hu : u = e₂.snd := splitSet_fst he d hd
        have h1 := splitFst_of_not_mem (symm_not_mem_splitSet (R := R) he hne)
        refine hiso _ ⟨e₁.symm, ?_, rfl⟩
        rw [h1, hu]
        exact congrArg some he
      · exact hiso _ ⟨d, splitFst_of_not_mem hd, rfl⟩
    · rintro hiso y ⟨d, h1, -⟩
      have hd : d ∉ R.splitSet e₁ e₂ := fun h ↦ by
        rw [splitFst_of_mem h] at h1
        exact Option.some_ne_none u h1.symm
      rw [splitFst_of_not_mem hd] at h1
      have hdu : d.fst = u := Option.some.inj h1
      exact hiso d.snd (hdu ▸ d.adj)

/-- The `χ` part of blueprint `lem:split2`: splitting at two corners of the same face increases
`χ` by 2. -/
theorem eulerChar_split (he : e₁.snd = e₂.snd) (hne : e₁ ≠ e₂)
    (hface : R.facePerm.SameCycle e₁ e₂) :
    (R.split he).eulerChar = R.eulerChar + 2 := by
  have : Fintype V := Fintype.ofFinite V
  have hcard : Nat.card (Option V) = Nat.card V + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option, Nat.card_eq_fintype_card]
  unfold eulerChar numFaces
  rw [orbitCount_split_facePerm he hne hface, ncard_edgeSet_splitGraph he,
    isolated_splitGraph he hne, Set.ncard_image_of_injective _ (Option.some_injective V), hcard]
  push_cast
  ring

end RotationSystem

/-! ### Connected components -/

section Components

/-- A map that transports reachability along each edge transports reachability (the vertex
types may differ). -/
theorem reachable_map_of_adj {α β : Type*} {H₁ : SimpleGraph α} {H₂ : SimpleGraph β} (f : α → β)
    (hf : ∀ a b, H₁.Adj a b → H₂.Reachable (f a) (f b)) {u v : α} (h : H₁.Reachable u v) :
    H₂.Reachable (f u) (f v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .refl _
  | cons hab _ ih => exact (hf _ _ hab).trans ih

/-- A set closed under edges is closed under reachability. -/
theorem mem_of_reachable_of_closed {α : Type*} {H : SimpleGraph α} (X : Set α)
    (hX : ∀ a b, a ∈ X → H.Adj a b → b ∈ X) {u v : α} (hu : u ∈ X) (h : H.Reachable u v) :
    v ∈ X := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons hab _ ih => exact ih (hX _ _ hu hab)

include hB in
/-- The reversal of a dart at `w` is not in `B`. -/
theorem symm_not_mem_of_fst_eq {d : G.Dart} (hd : d.fst = w) : d.symm ∉ B :=
  fun h ↦ d.adj.ne (hd.trans (hB _ h).symm)

/-- The homomorphism sending `none` to `w`. -/
noncomputable def splitHom : splitGraph B hB →g G where
  toFun x := x.elim w id
  map_rel' := by
    rintro x y ⟨d, rfl, rfl⟩
    have h1 : (splitFst B d).elim w id = d.fst := by
      by_cases hd : d ∈ B
      · rw [splitFst_of_mem hd]
        exact (hB d hd).symm
      · rw [splitFst_of_not_mem hd]
        rfl
    have h2 : (splitFst B d.symm).elim w id = d.snd := by
      by_cases hd : d.symm ∈ B
      · rw [splitFst_of_mem hd]
        exact (hB _ hd).symm
      · rw [splitFst_of_not_mem hd]
        rfl
    change G.Adj ((splitFst B d).elim w id) ((splitFst B d.symm).elim w id)
    rw [h1, h2]
    exact d.adj

/-- Splitting a vertex does not merge components: `c ≤ c'`. -/
theorem card_connectedComponent_le_split [Finite V] :
    Nat.card G.ConnectedComponent ≤ Nat.card (splitGraph B hB).ConnectedComponent := by
  apply Nat.card_le_card_of_surjective (ConnectedComponent.map (splitHom hB))
  intro c
  induction c using ConnectedComponent.ind with
  | h u => exact ⟨(splitGraph B hB).connectedComponentMk (some u), rfl⟩

/-- In a graph where `some w` and `none` are connected, original reachability transports along
`some`. -/
theorem reachable_some_of_reachable {H : SimpleGraph (Option V)} (hle : splitGraph B hB ≤ H)
    (hlink : H.Reachable (some w) none) {u v : V} (h : G.Reachable u v) :
    H.Reachable (some u) (some v) := by
  refine reachable_map_of_adj some (fun a b hab ↦ ?_) h
  let d : G.Dart := ⟨(a, b), hab⟩
  have hd : H.Adj (splitFst B d) (splitFst B d.symm) := hle ⟨d, rfl, rfl⟩
  have h1 : H.Reachable (some a) (splitFst B d) := by
    by_cases hdB : d ∈ B
    · rw [splitFst_of_mem hdB]
      have ha : a = w := hB d hdB
      rw [ha]
      exact hlink
    · rw [splitFst_of_not_mem hdB]
  have h2 : H.Reachable (splitFst B d.symm) (some b) := by
    by_cases hdB : d.symm ∈ B
    · rw [splitFst_of_mem hdB]
      have hb : b = w := hB _ hdB
      rw [hb]
      exact hlink.symm
    · rw [splitFst_of_not_mem hdB]
      exact .refl _
  exact h1.trans (hd.reachable.trans h2)

/-- If `some w` and `none` are connected, the number of components does not increase. -/
theorem card_connectedComponent_le_of_reachable [Finite V] {H : SimpleGraph (Option V)}
    (hle : splitGraph B hB ≤ H) (hlink : H.Reachable (some w) none) :
    Nat.card H.ConnectedComponent ≤ Nat.card G.ConnectedComponent := by
  let f : G.ConnectedComponent → H.ConnectedComponent :=
    ConnectedComponent.lift (fun u ↦ H.connectedComponentMk (some u))
      (fun u v p _ ↦ ConnectedComponent.eq.mpr
        (reachable_some_of_reachable hB hle hlink p.reachable))
  apply Nat.card_le_card_of_surjective f
  intro c
  induction c using ConnectedComponent.ind with
  | h x =>
    rcases x with _ | u
    · exact ⟨G.connectedComponentMk w, ConnectedComponent.eq.mpr hlink⟩
    · exact ⟨G.connectedComponentMk u, rfl⟩

/-- The linking condition: there are a dart `a` at `w` outside `B` and a dart `b` in `B` whose
end vertices are connected in `G - w`. -/
def SplitLinked (B : Set G.Dart) (w : V) : Prop :=
  ∃ a b : G.Dart, a.fst = w ∧ a ∉ B ∧ b ∈ B ∧ (deleteVertices G {w}).Reachable a.snd b.snd

theorem reachable_none_of_linked (h : SplitLinked B w) :
    (splitGraph B hB).Reachable (some w) none := by
  obtain ⟨a, b, ha, haB, hbB, hab⟩ := h
  have h1 : (splitGraph B hB).Adj (some w) (some a.snd) :=
    ⟨a, by rw [splitFst_of_not_mem haB, ha], splitFst_of_not_mem (symm_not_mem_of_fst_eq hB ha)⟩
  have h3 : (splitGraph B hB).Adj (some b.snd) none :=
    ⟨b.symm, splitFst_of_not_mem (symm_not_mem_of_fst_eq hB (hB b hbB)),
      by rw [Dart.symm_symm]; exact splitFst_of_mem hbB⟩
  have h2 : (splitGraph B hB).Reachable (some a.snd) (some b.snd) := by
    refine reachable_map_of_adj some (fun p q hpq ↦ ?_) hab
    obtain ⟨hpq, hp, hq⟩ := hpq
    let d : G.Dart := ⟨(p, q), hpq⟩
    have hdB : d ∉ B := fun h ↦ hp (Set.mem_singleton_iff.2 (hB d h))
    have hdB' : d.symm ∉ B := fun h ↦ hq (Set.mem_singleton_iff.2 (hB _ h))
    exact Adj.reachable ⟨d, splitFst_of_not_mem hdB, splitFst_of_not_mem hdB'⟩
  exact h1.reachable.trans (h2.trans h3.reachable)

/-- Conversely, if `some w` and `none` are connected, the linking condition holds. The proof uses
that the set of vertices reachable in `G - w` from the `A` side is closed under the edges of the
split graph. -/
theorem linked_of_reachable_none (h : (splitGraph B hB).Reachable (some w) none) :
    SplitLinked B w := by
  by_contra hno
  let X : Set (Option V) := {x | x = some w ∨ ∃ u, x = some u ∧ ∃ a : G.Dart, a.fst = w ∧
    a ∉ B ∧ (deleteVertices G {w}).Reachable a.snd u}
  have closed : ∀ x y, x ∈ X → (splitGraph B hB).Adj x y → y ∈ X := by
    rintro x y hx ⟨d, rfl, rfl⟩
    have hdB : d ∉ B := by
      intro hd
      rw [splitFst_of_mem hd] at hx
      rcases hx with hx | ⟨u, hu, -⟩
      · exact Option.some_ne_none w hx.symm
      · exact Option.some_ne_none u hu.symm
    rw [splitFst_of_not_mem hdB] at hx
    rcases hx with hx | ⟨u, hu, a, ha, haB, hau⟩
    · -- neighbors of `some w`
      have hdw : d.fst = w := Option.some.inj hx
      right
      exact ⟨d.snd, splitFst_of_not_mem (symm_not_mem_of_fst_eq hB hdw), d, hdw, hdB, .refl _⟩
    · have hdu : d.fst = u := Option.some.inj hu
      have huw : u ≠ w := by
        intro huw
        rw [huw] at hau
        have := eq_of_isIsolated_of_reachable
          (isIsolated_deleteVertices G (Set.mem_singleton w)) hau.symm
        exact a.adj.ne (ha.trans this.symm)
      by_cases hsw : d.snd = w
      · by_cases hsB : d.symm ∈ B
        · have hau' : (deleteVertices G {w}).Reachable a.snd d.symm.snd := by
            rw [show d.symm.snd = u from hdu]
            exact hau
          exact absurd ⟨a, d.symm, ha, haB, hsB, hau'⟩ hno
        · left
          rw [splitFst_of_not_mem hsB]
          exact congrArg some hsw
      · right
        have hsB : d.symm ∉ B := fun h ↦ hsw (hB _ h)
        refine ⟨d.snd, splitFst_of_not_mem hsB, a, ha, haB, hau.trans ?_⟩
        have hadj : G.Adj u d.snd := by
          rw [← hdu]
          exact d.adj
        exact Adj.reachable ⟨hadj, fun h ↦ huw (Set.mem_singleton_iff.1 h),
          fun h ↦ hsw (Set.mem_singleton_iff.1 h)⟩
  have hnone := mem_of_reachable_of_closed X closed (Or.inl rfl) h
  rcases hnone with h' | ⟨u, hu, -⟩
  · exact Option.some_ne_none w h'.symm
  · exact Option.some_ne_none u hu.symm

theorem reachable_none_iff_linked :
    (splitGraph B hB).Reachable (some w) none ↔ SplitLinked B w :=
  ⟨linked_of_reachable_none hB, reachable_none_of_linked hB⟩

/-- Under the linking condition, `c' = c`. -/
theorem card_connectedComponent_split_of_linked [Finite V] (h : SplitLinked B w) :
    Nat.card (splitGraph B hB).ConnectedComponent = Nat.card G.ConnectedComponent :=
  le_antisymm (card_connectedComponent_le_of_reachable hB le_rfl (reachable_none_of_linked hB h))
    (card_connectedComponent_le_split hB)

/-- The split graph has no edge between `some w` and `none`. -/
theorem not_adj_some_none : ¬ (splitGraph B hB).Adj (some w) none := by
  rintro ⟨d, h1, h2⟩
  have hdB : d ∉ B := fun h ↦ by
    rw [splitFst_of_mem h] at h1
    exact Option.some_ne_none w h1.symm
  rw [splitFst_of_not_mem hdB] at h1
  exact symm_not_mem_of_fst_eq hB (Option.some.inj h1) (splitFst_eq_none_iff.1 h2)

/-- Always `c' ≤ c + 1`, by comparison with the graph that adds an edge between `some w` and
`none`. -/
theorem card_connectedComponent_split_le [Finite V] :
    Nat.card (splitGraph B hB).ConnectedComponent ≤ Nat.card G.ConnectedComponent + 1 := by
  let H := splitGraph B hB ⊔ edge (some w) none
  have hlink : H.Reachable (some w) none :=
    Adj.reachable (Or.inr (by rw [edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, Option.some_ne_none w⟩))
  have hH : H.deleteEdges {s(some w, none)} = splitGraph B hB := by
    ext x y
    simp only [H, deleteEdges_adj, sup_adj, edge_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨h | ⟨h, -⟩, hne⟩
      · exact h
      · exfalso
        apply hne
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact not_adj_some_none hB h
      · exact not_adj_some_none hB h.symm
  have h1 := card_connectedComponent_deleteEdges_le H (some w) none
  rw [hH] at h1
  have h2 : Nat.card H.ConnectedComponent ≤ Nat.card G.ConnectedComponent :=
    card_connectedComponent_le_of_reachable hB le_sup_left hlink
  omega

/-- Without the linking condition, `c' = c + 1`. -/
theorem card_connectedComponent_split_of_not_linked [Finite V] (h : ¬ SplitLinked B w) :
    Nat.card (splitGraph B hB).ConnectedComponent = Nat.card G.ConnectedComponent + 1 := by
  have hle := card_connectedComponent_split_le hB
  have hge := card_connectedComponent_le_split hB
  by_contra hne
  have hsurj : Function.Surjective (ConnectedComponent.map (splitHom hB)) := by
    intro c
    induction c using ConnectedComponent.ind with
    | h u => exact ⟨(splitGraph B hB).connectedComponentMk (some u), rfl⟩
  have hbij := hsurj.bijective_of_nat_card_le (by omega)
  have heq : (splitGraph B hB).connectedComponentMk (some w) =
      (splitGraph B hB).connectedComponentMk none := hbij.1 rfl
  exact h (linked_of_reachable_none hB (ConnectedComponent.eq.mp heq))

end Components

namespace RotationSystem

variable [DecidableEq V] [Finite V] {R : RotationSystem G} {e₁ e₂ : G.Dart}

/-- Use in J1: for genus 0, splitting at two corners of the same face cannot satisfy the linking
condition. Otherwise `χ' = χ + 2 = 2c + 2` and `c' = c`, contradicting Euler's inequality
`χ' ≤ 2c'`. -/
theorem not_splitLinked_of_eulerChar (hR : R.eulerChar = 2 * Nat.card G.ConnectedComponent)
    (he : e₁.snd = e₂.snd) (hne : e₁ ≠ e₂) (hface : R.facePerm.SameCycle e₁ e₂) :
    ¬ SplitLinked (R.splitSet e₁ e₂) e₂.snd := by
  intro hl
  have hχ := eulerChar_split he hne hface
  have hc := card_connectedComponent_split_of_linked (splitSet_fst he) hl
  have hle := (R.split he).eulerChar_le
  rw [hχ, hR, hc] at hle
  omega

end RotationSystem

end Kuratowski
