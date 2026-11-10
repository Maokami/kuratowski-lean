import Kuratowski.ContractCounts
import Kuratowski.PermutationDeletion

/-!
# Adding an edge between two corners of one face (blueprint `lem:add_edge`)

Let `R` be a rotation system and `a`, `c` darts whose start vertices `u`, `v` are distinct and
non-adjacent, with `ā`, `c̄` in the same face cycle. We build a rotation system `R₁` of
`G ⊔ edge u v` by inserting `(u, v)` after `a` and `(v, u)` after `c`, keeping all other rotations.
The number of face cycles increases by one and genus 0 is preserved.

* The darts of the new graph are the old darts (`ι`) together with `(u, v)` and `(v, u)`.
* `ρ₁ = τ (ι a, uv) (ι c, vu)`, where `τ` is the transported `ρ` with the two new darts fixed.
* `φ₁ = τσ (ι ā, vu) (ι c̄, uv)`: the first transposition merges with the 2-cycle `(uv vu)` (−1)
  and the second splits a cycle (+1). `τσ` is the transported `φ` plus a 2-cycle, so it has
  `O + 1` cycles.
-/

namespace Kuratowski

open SimpleGraph Equiv Equiv.Perm Function

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Data for adding an edge between two corners of the same face. -/
structure AddEdgeData (G : SimpleGraph V) where
  R : RotationSystem G
  a : G.Dart
  c : G.Dart
  hne : a.fst ≠ c.fst
  hn : ¬ G.Adj a.fst c.fst
  hface : R.facePerm.SameCycle a.symm c.symm

namespace AddEdgeData

variable (D : AddEdgeData G)

/-- The graph with the new edge, `G ⊔ edge u v`. -/
abbrev graph : SimpleGraph V := G ⊔ edge D.a.fst D.c.fst

/-- The new dart `(u, v)`. -/
def uvDart : D.graph.Dart :=
  ⟨(D.a.fst, D.c.fst), Or.inr ((edge_adj _ _ _ _).2 ⟨Or.inl ⟨rfl, rfl⟩, D.hne⟩)⟩

/-- The new dart `(v, u)`. -/
def vuDart : D.graph.Dart :=
  ⟨(D.c.fst, D.a.fst), Or.inr ((edge_adj _ _ _ _).2 ⟨Or.inr ⟨rfl, rfl⟩, D.hne.symm⟩)⟩

/-- An old dart viewed as a dart of the new graph. -/
def ι (d : G.Dart) : D.graph.Dart := ⟨d.toProd, Or.inl d.adj⟩

/-- Darts of the new graph other than the two new darts. -/
abbrev Old := {d : D.graph.Dart // d.toProd ≠ (D.a.fst, D.c.fst) ∧ d.toProd ≠ (D.c.fst, D.a.fst)}

omit [DecidableEq V] in
theorem ι_mem (d : G.Dart) :
    (D.ι d).toProd ≠ (D.a.fst, D.c.fst) ∧ (D.ι d).toProd ≠ (D.c.fst, D.a.fst) := by
  refine ⟨fun h ↦ D.hn ?_, fun h ↦ D.hn ?_⟩
  · have hd := d.adj
    rw [show d.toProd = (D.a.fst, D.c.fst) from h] at hd
    exact hd
  · have hd := d.adj
    rw [show d.toProd = (D.c.fst, D.a.fst) from h] at hd
    exact hd.symm

/-- The corresponding old dart. -/
def ofOld (s : D.Old) : G.Dart :=
  ⟨s.1.toProd, s.1.adj.resolve_right fun h ↦ by
    rcases ((edge_adj _ _ _ _).1 h).1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact s.2.1 (Prod.ext h1 h2)
    · exact s.2.2 (Prod.ext h1 h2)⟩

/-- Bijection between the old darts and the darts other than the two new ones. -/
def oldEquiv : G.Dart ≃ D.Old where
  toFun d := ⟨D.ι d, D.ι_mem d⟩
  invFun := D.ofOld
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq V] in
theorem ι_injective : Injective D.ι := by
  intro d e h
  have h' := congrArg Dart.toProd h
  exact Dart.ext _ _ h'

omit [DecidableEq V] in
theorem ι_ne_uv (d : G.Dart) : D.ι d ≠ D.uvDart := fun h ↦ (D.ι_mem d).1 (by rw [h]; rfl)

omit [DecidableEq V] in
theorem ι_ne_vu (d : G.Dart) : D.ι d ≠ D.vuDart := fun h ↦ (D.ι_mem d).2 (by rw [h]; rfl)

omit [DecidableEq V] in
theorem uv_ne_vu : D.uvDart ≠ D.vuDart := fun h ↦ D.hne (congrArg (·.fst) h)

omit [DecidableEq V] in
theorem ι_a_ne_ι_c : D.ι D.a ≠ D.ι D.c := fun h ↦ D.hne (congrArg (·.fst) h)

/-- A dart of the new graph is an old dart or one of the two new darts. -/
theorem dart_cases (d : D.graph.Dart) : (∃ e, d = D.ι e) ∨ d = D.uvDart ∨ d = D.vuDart := by
  by_cases h1 : d.toProd = (D.a.fst, D.c.fst)
  · exact Or.inr (Or.inl (Dart.ext _ _ h1))
  by_cases h2 : d.toProd = (D.c.fst, D.a.fst)
  · exact Or.inr (Or.inr (Dart.ext _ _ h2))
  exact Or.inl ⟨D.ofOld ⟨d, h1, h2⟩, rfl⟩

/-- The transported rotation; the two new darts are fixed points. -/
def τ : Perm D.graph.Dart := Perm.ofSubtype (D.oldEquiv.permCongr D.R.rot)

theorem τ_ι (d : G.Dart) : D.τ (D.ι d) = D.ι (D.R.rot d) := by
  unfold τ
  rw [Perm.ofSubtype_apply_of_mem (D.oldEquiv.permCongr D.R.rot) (D.ι_mem d)]
  rfl

theorem τ_uv : D.τ D.uvDart = D.uvDart :=
  Perm.ofSubtype_apply_of_not_mem _ (by simp [uvDart])

theorem τ_vu : D.τ D.vuDart = D.vuDart :=
  Perm.ofSubtype_apply_of_not_mem _ (by simp [vuDart])

theorem τ_pow_ι (d : G.Dart) (n : ℕ) : (D.τ ^ n) (D.ι d) = D.ι ((D.R.rot ^ n) d) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, ih, τ_ι, pow_succ', Perm.mul_apply]

/-- The new rotation: insert `(u, v)` after `a` and `(v, u)` after `c`. -/
def rot : Perm D.graph.Dart := D.τ * swap (D.ι D.a) D.uvDart * swap (D.ι D.c) D.vuDart

theorem rot_ι_a : D.rot (D.ι D.a) = D.uvDart := by
  rw [rot, Perm.mul_apply, swap_apply_of_ne_of_ne D.ι_a_ne_ι_c (D.ι_ne_vu D.a), Perm.mul_apply,
    swap_apply_left, τ_uv]

theorem rot_uv : D.rot D.uvDart = D.ι (D.R.rot D.a) := by
  rw [rot, Perm.mul_apply, swap_apply_of_ne_of_ne (D.ι_ne_uv D.c).symm D.uv_ne_vu, Perm.mul_apply,
    swap_apply_right, τ_ι]

theorem rot_ι_c : D.rot (D.ι D.c) = D.vuDart := by
  rw [rot, Perm.mul_apply, swap_apply_left, Perm.mul_apply,
    swap_apply_of_ne_of_ne (D.ι_ne_vu D.a).symm D.uv_ne_vu.symm, τ_vu]

theorem rot_vu : D.rot D.vuDart = D.ι (D.R.rot D.c) := by
  rw [rot, Perm.mul_apply, swap_apply_right, Perm.mul_apply,
    swap_apply_of_ne_of_ne D.ι_a_ne_ι_c.symm (D.ι_ne_uv D.c), τ_ι]

theorem rot_ι_of_ne {e : G.Dart} (ha : e ≠ D.a) (hc : e ≠ D.c) :
    D.rot (D.ι e) = D.ι (D.R.rot e) := by
  have ha' : D.ι e ≠ D.ι D.a := fun h ↦ ha (D.ι_injective h)
  have hc' : D.ι e ≠ D.ι D.c := fun h ↦ hc (D.ι_injective h)
  rw [rot, Perm.mul_apply, swap_apply_of_ne_of_ne hc' (D.ι_ne_vu e), Perm.mul_apply,
    swap_apply_of_ne_of_ne ha' (D.ι_ne_uv e), τ_ι]

theorem fst_rot (d : D.graph.Dart) : (D.rot d).fst = d.fst := by
  rcases D.dart_cases d with ⟨e, rfl⟩ | rfl | rfl
  · by_cases ha : e = D.a
    · subst ha
      rw [rot_ι_a]
      rfl
    by_cases hc : e = D.c
    · subst hc
      rw [rot_ι_c]
      rfl
    rw [D.rot_ι_of_ne ha hc]
    exact D.R.fst_rot e
  · rw [rot_uv]
    exact D.R.fst_rot D.a
  · rw [rot_vu]
    exact D.R.fst_rot D.c

variable [Finite V]

theorem τ_sameCycle {d e : G.Dart} (h : d.fst = e.fst) : D.τ.SameCycle (D.ι d) (D.ι e) := by
  obtain ⟨n, hn⟩ := (D.R.sameCycle_rot d e h).exists_nat_pow_eq
  exact ⟨n, by rw [zpow_natCast, τ_pow_ι, hn]⟩

theorem sameCycle_rot (d d' : D.graph.Dart) (h : d.fst = d'.fst) : D.rot.SameCycle d d' := by
  set f₁ := D.τ * swap (D.ι D.a) D.uvDart with hf₁
  have hX : ¬ D.τ.SameCycle (D.ι D.a) D.uvDart := fun hs ↦ D.ι_ne_uv D.a (hs.eq_of_right D.τ_uv)
  have hx := sameCycle_mul_swap_of_not hX
  have hf₁vu : f₁ D.vuDart = D.vuDart := by
    rw [hf₁, Perm.mul_apply, swap_apply_of_ne_of_ne (D.ι_ne_vu D.a).symm D.uv_ne_vu.symm, τ_vu]
  have hY : ¬ f₁.SameCycle (D.ι D.c) D.vuDart := fun hs ↦ D.ι_ne_vu D.c (hs.eq_of_right hf₁vu)
  have hy := sameCycle_mul_swap_of_not hY
  have keep {p q : D.graph.Dart} (hpq : D.τ.SameCycle p q) : D.rot.SameCycle p q :=
    hy.mul_swap_of_sameCycle (hx.mul_swap_of_sameCycle hpq)
  have hau : D.rot.SameCycle (D.ι D.a) D.uvDart := hy.mul_swap_of_sameCycle hx
  have hcv : D.rot.SameCycle (D.ι D.c) D.vuDart := hy
  -- send each dart to an old dart with the same start vertex
  have base : ∀ d : D.graph.Dart, ∃ e : G.Dart, e.fst = d.fst ∧ D.rot.SameCycle d (D.ι e) := by
    intro d
    rcases D.dart_cases d with ⟨e, rfl⟩ | rfl | rfl
    · exact ⟨e, rfl, .refl _ _⟩
    · exact ⟨D.a, rfl, hau.symm⟩
    · exact ⟨D.c, rfl, hcv.symm⟩
  obtain ⟨e, he, hde⟩ := base d
  obtain ⟨e', he', hde'⟩ := base d'
  exact hde.trans ((keep (D.τ_sameCycle (he.trans (h.trans he'.symm)))).trans hde'.symm)

/-- The rotation system of the graph with the new edge. -/
def rotationSystem : RotationSystem D.graph where
  rot := D.rot
  fst_rot := D.fst_rot
  sameCycle_rot := D.sameCycle_rot

/-! ### Number of face cycles -/

/-- Dart reversal in the new graph. -/
def rev : Perm D.graph.Dart := Function.Involutive.toPerm _ Dart.symm_involutive

omit [DecidableEq V] [Finite V] in
theorem rev_involutive : Involutive D.rev := Dart.symm_involutive

theorem facePerm_eq : D.rotationSystem.facePerm = D.rot * D.rev := Equiv.ext fun _ ↦ rfl

omit [Finite V] in
theorem f_ι (d : G.Dart) : (D.τ * D.rev) (D.ι d) = D.ι (D.R.facePerm d) := by
  rw [Perm.mul_apply, show D.rev (D.ι d) = D.ι d.symm from rfl, τ_ι]
  rfl

omit [Finite V] in
theorem f_uv : (D.τ * D.rev) D.uvDart = D.vuDart := by
  rw [Perm.mul_apply, show D.rev D.uvDart = D.vuDart from rfl, τ_vu]

omit [Finite V] in
theorem f_vu : (D.τ * D.rev) D.vuDart = D.uvDart := by
  rw [Perm.mul_apply, show D.rev D.vuDart = D.uvDart from rfl, τ_uv]

omit [Finite V] in
theorem f_pow_ι (d : G.Dart) (n : ℕ) :
    ((D.τ * D.rev) ^ n) (D.ι d) = D.ι ((D.R.facePerm ^ n) d) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, ih, f_ι, pow_succ', Perm.mul_apply]

/-- `τσ` has the cycles of the transported `φ` plus one 2-cycle. -/
theorem orbitCount_f : orbitCount (D.τ * D.rev) = orbitCount D.R.facePerm + 1 := by
  set g := D.τ * D.rev * swap D.uvDart D.vuDart with hg
  have hguv : g D.uvDart = D.uvDart := by rw [hg, Perm.mul_apply, swap_apply_left, f_vu]
  have hgvu : g D.vuDart = D.vuDart := by rw [hg, Perm.mul_apply, swap_apply_right, f_uv]
  have hgι : ∀ d : G.Dart, g (D.ι d) = D.ι (D.R.facePerm d) := by
    intro d
    rw [hg, Perm.mul_apply, swap_apply_of_ne_of_ne (D.ι_ne_uv d) (D.ι_ne_vu d), f_ι]
  have hP : ∀ d, (g d).toProd ≠ (D.a.fst, D.c.fst) ∧ (g d).toProd ≠ (D.c.fst, D.a.fst) ↔
      d.toProd ≠ (D.a.fst, D.c.fst) ∧ d.toProd ≠ (D.c.fst, D.a.fst) := by
    intro d
    rcases D.dart_cases d with ⟨e, rfl⟩ | rfl | rfl
    · rw [hgι]
      exact iff_of_true (D.ι_mem _) (D.ι_mem e)
    · rw [hguv]
    · rw [hgvu]
  have h1 := orbitCount_eq_subtypePerm_add g
    (fun d : D.graph.Dart ↦ d.toProd ≠ (D.a.fst, D.c.fst) ∧ d.toProd ≠ (D.c.fst, D.a.fst)) hP (by
      intro d hd
      rcases D.dart_cases d with ⟨e, rfl⟩ | rfl | rfl
      · exact absurd (D.ι_mem e) hd
      · exact hguv
      · exact hgvu)
  have h2 : g.subtypePerm hP = D.oldEquiv.permCongr D.R.facePerm :=
    Equiv.ext fun s ↦ Subtype.ext (by
      change g s.1 = D.ι (D.R.facePerm (D.ofOld s))
      rw [show s.1 = D.ι (D.ofOld s) from rfl, hgι])
  have h3 : Nat.card {d : D.graph.Dart //
      ¬ (d.toProd ≠ (D.a.fst, D.c.fst) ∧ d.toProd ≠ (D.c.fst, D.a.fst))} = 2 := by
    have hs : {d : D.graph.Dart |
        ¬ (d.toProd ≠ (D.a.fst, D.c.fst) ∧ d.toProd ≠ (D.c.fst, D.a.fst))} =
        {D.uvDart, D.vuDart} := by
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_and_or,
        not_not]
      constructor
      · rintro (h | h)
        · exact Or.inl (Dart.ext _ _ h)
        · exact Or.inr (Dart.ext _ _ h)
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
    change Nat.card ↥{d : D.graph.Dart |
      ¬ (d.toProd ≠ (D.a.fst, D.c.fst) ∧ d.toProd ≠ (D.c.fst, D.a.fst))} = 2
    rw [Nat.card_coe_set_eq, hs, Set.ncard_pair D.uv_ne_vu]
  have h4 : orbitCount (g * swap D.uvDart D.vuDart) + 1 = orbitCount g :=
    orbitCount_mul_swap_of_not_sameCycle fun h ↦ D.uv_ne_vu (h.eq_of_left hguv)
  have h5 : g * swap D.uvDart D.vuDart = D.τ * D.rev := by
    rw [hg, mul_assoc, swap_mul_self, mul_one]
  rw [h2, orbitCount_permCongr, h3] at h1
  rw [h5] at h4
  omega

/-- Face count of blueprint `lem:add_edge`: joining two corners of one face adds one face
cycle. -/
theorem orbitCount_facePerm :
    orbitCount D.rotationSystem.facePerm = orbitCount D.R.facePerm + 1 := by
  have hface : D.rot * D.rev = D.τ * D.rev * swap (D.ι D.a.symm) D.vuDart *
      swap (D.ι D.c.symm) D.uvDart :=
    PermutationDeletion.swaps_comp_involution D.τ D.rev D.rev_involutive _ _ _ _
  have h0 := D.orbitCount_f
  set f := D.τ * D.rev with hf
  have hā_uv : D.ι D.a.symm ≠ D.uvDart := D.ι_ne_uv _
  have hā_vu : D.ι D.a.symm ≠ D.vuDart := D.ι_ne_vu _
  have hn1 : ¬ f.SameCycle (D.ι D.a.symm) D.vuDart := fun h ↦
    PermutationDeletion.not_sameCycle_of_two_cycle f D.f_vu D.f_uv hā_vu hā_uv h.symm
  have h1 := orbitCount_mul_swap_of_not_sameCycle hn1
  have hj := sameCycle_mul_swap_of_not hn1
  obtain ⟨n, hn⟩ := D.hface.exists_nat_pow_eq
  have hca : f.SameCycle (D.ι D.a.symm) (D.ι D.c.symm) :=
    ⟨n, by rw [zpow_natCast, hf, f_pow_ι, hn]⟩
  have hvu : f.SameCycle D.vuDart D.uvDart := ⟨1, by rw [zpow_one, hf, f_vu]⟩
  have hs : (f * swap (D.ι D.a.symm) D.vuDart).SameCycle (D.ι D.c.symm) D.uvDart :=
    (hj.mul_swap_of_sameCycle hca).symm.trans (hj.trans (hj.mul_swap_of_sameCycle hvu))
  have h2 := orbitCount_mul_swap_of_sameCycle (D.ι_ne_uv _) hs
  rw [facePerm_eq, hface]
  omega

/-! ### Counts and genus -/

omit [DecidableEq V] in
theorem reachable : G.Reachable D.a.fst D.c.fst := by
  have key : ∀ n : ℕ, G.Reachable D.a.symm.fst ((D.R.facePerm ^ n) D.a.symm).fst := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply, RotationSystem.facePerm_fst]
      exact ih.trans ((D.R.facePerm ^ n) D.a.symm).adj.reachable
  obtain ⟨n, hn⟩ := D.hface.exists_nat_pow_eq
  have h := key n
  rw [hn] at h
  exact D.a.adj.reachable.trans (h.trans D.c.adj.reachable.symm)

theorem eulerChar_rotationSystem : D.rotationSystem.eulerChar = D.R.eulerChar := by
  have hO := D.orbitCount_facePerm
  have hE := ncard_edgeSet_sup_edge D.hne D.hn
  have hI := ncard_isolated_sup_edge (G := G) (fun h ↦ h _ D.a.adj) (fun h ↦ h _ D.c.adj)
  unfold RotationSystem.eulerChar RotationSystem.numFaces
  rw [hO, hE, hI]
  push_cast
  omega

/-- Blueprint `lem:add_edge`: if `R` has genus 0, so does the rotation system with the new
edge. -/
theorem eulerChar_eq (hR : D.R.eulerChar = 2 * Nat.card G.ConnectedComponent) :
    D.rotationSystem.eulerChar = 2 * Nat.card D.graph.ConnectedComponent := by
  rw [D.eulerChar_rotationSystem, hR, card_connectedComponent_sup_edge_of_reachable D.reachable]

/-! ### Public rotation formulas -/

theorem rotationSystem_rot (d : D.graph.Dart) : D.rotationSystem.rot d = D.rot d := rfl

/-- The rotation of an old dart `e ≠ a, c` is unchanged (stated via `toProd`). -/
theorem rotationSystem_rot_toProd_of_ne (d : D.graph.Dart) (e : G.Dart) (hde : d.toProd = e.toProd)
    (ha : e ≠ D.a) (hc : e ≠ D.c) : (D.rotationSystem.rot d).toProd = (D.R.rot e).toProd := by
  rw [show d = D.ι e from Dart.ext _ _ hde, rotationSystem_rot, D.rot_ι_of_ne ha hc]
  rfl

end AddEdgeData

/-- Blueprint `lem:add_edge`. Adding an edge between two corners of the same face gives a
rotation system with one more face cycle that preserves genus 0. The rotation formulas are the
`rot_*` lemmas of `AddEdgeData`. -/
theorem RotationSystem.exists_addEdge [Finite V] (R : RotationSystem G) {a c : G.Dart}
    (hne : a.fst ≠ c.fst) (hn : ¬ G.Adj a.fst c.fst) (hface : R.facePerm.SameCycle a.symm c.symm) :
    ∃ R₁ : RotationSystem (G ⊔ edge a.fst c.fst),
      orbitCount R₁.facePerm = orbitCount R.facePerm + 1 ∧
      (R.eulerChar = 2 * Nat.card G.ConnectedComponent →
        R₁.eulerChar = 2 * Nat.card (G ⊔ edge a.fst c.fst).ConnectedComponent) :=
  let D : AddEdgeData G := ⟨R, a, c, hne, hn, hface⟩
  ⟨D.rotationSystem, D.orbitCount_facePerm, D.eulerChar_eq⟩

end Kuratowski
