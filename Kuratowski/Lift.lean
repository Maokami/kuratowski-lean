import Kuratowski.AlternatingNeighbors
import Kuratowski.NonPlanar
import Kuratowski.PathsBuild
import Kuratowski.WalkLift
import Mathlib.Data.Fin.VecNotation

/-!
# Contraction preserves Kuratowski-freeness (blueprint `lem:lift`)

If `x ∼ y` and `G` contains no subdivision of `K₅` or `K₃,₃` (KF), then `G/xy` is KF
(`kuratowskiFree_contractEdge`). We prove the contrapositive. A path system in `G/xy` (the forward
direction needs no finiteness) is lifted to `G`; since `K₅` and `K₃,₃` have finitely many vertices,
`containsSubdivision_of_finite` gives a subdivision. The vertex type of `G` need not be finite.

* `SubdivisionPaths.ofFamily`: builds a path system from paths in all directions, without the
  symmetry condition.
* Case A (`nonempty_lift_of_not_branch`): if `x` is not a branch vertex, lift each path with
  `liftPath`. At most one undirected edge has a path through `x`, and `y` is inserted only into
  that path.
* Case B (`nonempty_lift_of_branch`): if `x = P.branch a₀`, choose a new branch vertex
  `t ∈ {x, y}`. If at most one path from `a₀` has a first edge not meeting `t`, the other vertex is
  inserted only into that path.
* Case C (`containsSubdivision_K33_of_split`): if each of the two kinds of bad paths occurs at
  least twice, split the branch vertex `x` into `x` and `y` to obtain `K₃,₃`. The two sides are
  `{x, f b₁, f b₂}` and `{y, f a₁, f a₂}`, and the paths are `xy`, `x → f aⱼ`, `f bᵢ → y`, and the
  four original paths `bᵢ — aⱼ`.
* A path whose first edge does not meet `x` meets `y`, so the two kinds of bad paths are different
  (`nonempty_lift_or_split`). Case C cannot occur for `K₃,₃`, whose degree is 3, and for `K₅` it
  yields `K₃,₃`.
-/


namespace Kuratowski

open SimpleGraph

namespace SubdivisionPaths

variable {V W : Type*} {K : SimpleGraph W} {G : SimpleGraph V}

/-- Build a path system from paths in all directions, without the symmetry condition. For finite
`W`, choose a linear order and use only the paths in one direction via `ofLT`. -/
noncomputable def ofFamily [Finite W] (f : W ↪ V) (q : ∀ a b, K.Adj a b → G.Walk (f a) (f b))
    (hp : ∀ a b (h : K.Adj a b), (q a b h).IsPath)
    (hint : ∀ a b (h : K.Adj a b), ∀ z ∈ walkInterior (q a b h), z ∉ Set.range f)
    (hdisj : ∀ a b (h : K.Adj a b) c d (h' : K.Adj c d), s(a, b) ≠ s(c, d) →
      Disjoint (walkInterior (q a b h)) (walkInterior (q c d h'))) :
    SubdivisionPaths K G :=
  letI : LinearOrder W := LinearOrder.lift' (Finite.equivFin W) (Finite.equivFin W).injective
  ofLT f (fun a b _ h ↦ q a b h) (fun a b _ h ↦ hp a b h) (fun a b _ h ↦ hint a b h)
    (fun a b _ h c d _ h' ↦ hdisj a b h c d h')

@[simp] theorem ofFamily_branch [Finite W] (f : W ↪ V) (q) (hp) (hint) (hdisj) :
    (ofFamily (K := K) (G := G) f q hp hint hdisj).branch = f := rfl

end SubdivisionPaths

section Lift

variable {V W : Type*} {K : SimpleGraph W} {G : SimpleGraph V} {x y : V}

/-- If `y` lies on a lifted path, the original path passes through `x`. -/
theorem mem_support_of_y_mem_liftPath [DecidableEq V] (hxy : G.Adj x y) {u v : V}
    (q : (contractEdge G x y).Walk u v) (hu : u ≠ y) (hy : y ∈ (liftPath hxy q).support) :
    x ∈ q.support := by
  by_contra hx
  exact not_mem_support_contractEdge q hu (mem_support_liftPath_of_not_mem hxy q hx hy)

/-- Case A: if `x` is not a branch vertex, lift every path. -/
theorem SubdivisionPaths.nonempty_lift_of_not_branch [Finite W] (hxy : G.Adj x y)
    (P : SubdivisionPaths K (contractEdge G x y)) (hx : x ∉ Set.range P.branch)
    (hy : y ∉ Set.range P.branch) : Nonempty (SubdivisionPaths K G) := by
  classical
  have hby : ∀ a, P.branch a ≠ y := fun a e ↦ hy ⟨a, e⟩
  -- interior of a lifted path: the original interior, or `y` when the original path passes `x`
  have key : ∀ a b (h : K.Adj a b), ∀ z ∈ walkInterior (liftPath hxy (P.path a b h)),
      z ∈ walkInterior (P.path a b h) ∨ (z = y ∧ x ∈ walkInterior (P.path a b h)) := by
    intro a b h z hz
    rcases walkInterior_liftPath_subset hxy _ hz with hz' | rfl
    · exact Or.inl hz'
    · refine Or.inr ⟨rfl, mem_support_of_y_mem_liftPath hxy _ (hby a) hz.1, ?_, ?_⟩
      · exact fun e ↦ hx ⟨a, e.symm⟩
      · exact fun e ↦ hx ⟨b, e.symm⟩
  refine ⟨SubdivisionPaths.ofFamily P.branch (fun a b h ↦ liftPath hxy (P.path a b h))
    (fun a b h ↦ liftPath_isPath hxy _) ?_ ?_⟩
  · intro a b h z hz
    rcases key a b h z hz with hz' | ⟨rfl, -⟩
    · exact P.interior_not_branch a b h z hz'
    · exact hy
  · intro a b h c d h' hne
    rw [Set.disjoint_left]
    intro z hz1 hz2
    rcases key a b h z hz1 with h1 | ⟨rfl, hx1⟩ <;> rcases key c d h' z hz2 with h2 | ⟨e, hx2⟩
    · exact Set.disjoint_left.1 (P.disjoint a b h c d h' hne) h1 h2
    · exact not_mem_support_contractEdge _ (hby a) (e ▸ h1.1)
    · exact not_mem_support_contractEdge _ (hby c) h2.1
    · exact Set.disjoint_left.1 (P.disjoint a b h c d h' hne) hx1 hx2

/-- Case B: if `x = P.branch a₀` and at most one path from `a₀` has a first edge not meeting the
new branch vertex `t ∈ {x, y}`, the path system lifts. Only that path gets the vertex of `{x, y}`
other than `t` inserted. -/
theorem SubdivisionPaths.nonempty_lift_of_branch [Finite W] (hxy : G.Adj x y)
    (P : SubdivisionPaths K (contractEdge G x y)) {a₀ : W} (hxa : P.branch a₀ = x)
    (hy : y ∉ Set.range P.branch) {t : V} (ht : t = x ∨ t = y)
    (hone : ∀ c c' (h : K.Adj a₀ c) (h' : K.Adj a₀ c'),
      ¬ G.Adj t (P.path a₀ c h).snd → ¬ G.Adj t (P.path a₀ c' h').snd → c = c') :
    Nonempty (SubdivisionPaths K G) := by
  classical
  have hby : ∀ a, P.branch a ≠ y := fun a e ↦ hy ⟨a, e⟩
  have hbx : ∀ a, a ≠ a₀ → P.branch a ≠ x :=
    fun a ha e ↦ ha (P.branch.injective (e.trans hxa.symm))
  have htb : ∀ a, a ≠ a₀ → t ≠ P.branch a := by
    intro a ha e
    rcases ht with rfl | rfl
    · exact hbx a ha e.symm
    · exact hby a e.symm
  -- the new branch vertices
  let g : W → V := Function.update P.branch a₀ t
  have hg : Function.Injective g := by
    intro a b hab
    by_cases ha : a = a₀ <;> by_cases hb : b = a₀
    · rw [ha, hb]
    · simp only [g, ha, Function.update_self, Function.update_of_ne hb] at hab
      exact absurd hab (htb b hb)
    · simp only [g, hb, Function.update_self, Function.update_of_ne ha] at hab
      exact absurd hab.symm (htb a ha)
    · simp only [g, Function.update_of_ne ha, Function.update_of_ne hb] at hab
      exact P.branch.injective hab
  let f : W ↪ V := ⟨g, hg⟩
  have hfa : f a₀ = t := Function.update_self _ _ _
  have hfo : ∀ a, a ≠ a₀ → f a = P.branch a := fun a ha ↦ Function.update_of_ne ha _ _
  -- lifting the paths leaving `a₀`
  have hlift : ∀ c (h : K.Adj a₀ c), ∃ r : G.Walk t (P.branch c), r.IsPath ∧
      ∀ z ∈ r.support, z = t ∨ (z ∈ (P.path a₀ c h).support ∧ z ≠ x) ∨
        ((z = x ∨ z = y) ∧ ¬ G.Adj t (P.path a₀ c h).snd) := by
    intro c h
    obtain ⟨r, hr, hs⟩ := exists_liftFrom hxy ht ((P.path a₀ c h).copy hxa rfl)
      ((Walk.isPath_copy _ _ _).2 (P.isPath a₀ c h)) (hbx c h.ne.symm)
    refine ⟨r, hr, fun z hz ↦ ?_⟩
    simpa [Walk.support_copy] using hs z hz
  choose R hRp hRs using hlift
  have hRint : ∀ c (h : K.Adj a₀ c), ∀ z ∈ walkInterior (R c h),
      z ∈ walkInterior (P.path a₀ c h) ∨
        (z ≠ t ∧ (z = x ∨ z = y) ∧ ¬ G.Adj t (P.path a₀ c h).snd) := by
    intro c h z hz
    rcases hRs c h z hz.1 with e | ⟨hs, hzx⟩ | ⟨hxy', hv⟩
    · exact absurd e hz.2.1
    · exact Or.inl ⟨hs, by rwa [hxa], hz.2.2⟩
    · exact Or.inr ⟨hz.2.1, hxy', hv⟩
  have hne₀ : ∀ {a b}, K.Adj a b → a = a₀ → b ≠ a₀ := fun h ha hb ↦ h.ne (ha.trans hb.symm)
  let q : ∀ a b, K.Adj a b → G.Walk (f a) (f b) := fun a b h ↦
    if ha : a = a₀ then
      (R b (ha ▸ h)).copy (by rw [ha, hfa]) (hfo b (hne₀ h ha)).symm
    else if hb : b = a₀ then
      (R a (hb ▸ h.symm)).reverse.copy (hfo a ha).symm (by rw [hb, hfa])
    else (liftPath hxy (P.path a b h)).copy (hfo a ha).symm (hfo b hb).symm
  have hxnot : ∀ a b (h : K.Adj a b), a ≠ a₀ → b ≠ a₀ → x ∉ (P.path a b h).support := by
    intro a b h ha hb hx
    have hxi : x ∈ walkInterior (P.path a b h) := ⟨hx, (hbx a ha).symm, (hbx b hb).symm⟩
    exact P.interior_not_branch a b h x hxi ⟨a₀, hxa⟩
  have key : ∀ a b (h : K.Adj a b), ∀ z ∈ walkInterior (q a b h),
      z ∈ walkInterior (P.path a b h) ∨ (z ≠ t ∧ (z = x ∨ z = y) ∧
        ∃ c, ∃ hc : K.Adj a₀ c, s(a, b) = s(a₀, c) ∧ ¬ G.Adj t (P.path a₀ c hc).snd) := by
    intro a b h z hz
    by_cases ha : a = a₀
    · subst ha
      simp only [q, ↓reduceDIte, walkInterior_copy] at hz
      rcases hRint b h z hz with h1 | ⟨h1, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2, b, h, rfl, h3⟩
    by_cases hb : b = a₀
    · subst hb
      simp only [q, ha, ↓reduceDIte, walkInterior_copy, walkInterior_reverse] at hz
      rcases hRint a h.symm z hz with h1 | ⟨h1, h2, h3⟩
      · left
        rwa [P.walkInterior_path_symm] at h1
      · exact Or.inr ⟨h1, h2, a, h.symm, Sym2.eq_swap, h3⟩
    · simp only [q, ha, hb, ↓reduceDIte, walkInterior_copy] at hz
      exact Or.inl (walkInterior_liftPath_subset_of_not_mem hxy _ (hxnot a b h ha hb) hz)
  -- vertices of the original interiors are neither `x` nor `y`
  have horig : ∀ a b (h : K.Adj a b), ∀ z ∈ walkInterior (P.path a b h), z ≠ x ∧ z ≠ y := by
    intro a b h z hz
    refine ⟨fun e ↦ P.interior_not_branch a b h z hz ⟨a₀, hxa.trans e.symm⟩, fun e ↦ ?_⟩
    exact not_mem_support_contractEdge _ (hby a) (e ▸ hz.1)
  refine ⟨SubdivisionPaths.ofFamily f q ?_ ?_ ?_⟩
  · intro a b h
    by_cases ha : a = a₀
    · subst ha
      simp only [q, ↓reduceDIte, Walk.isPath_copy]
      exact hRp b _
    by_cases hb : b = a₀
    · subst hb
      simp only [q, ha, ↓reduceDIte, Walk.isPath_copy, Walk.isPath_reverse_iff]
      exact hRp a _
    · simp only [q, ha, hb, ↓reduceDIte, Walk.isPath_copy]
      exact liftPath_isPath hxy _
  · intro a b h z hz
    rintro ⟨c, rfl⟩
    by_cases hc : c = a₀
    · subst hc
      rw [hfa] at hz
      rcases key a b h _ hz with h1 | ⟨h1, -⟩
      · rcases ht with e | e
        · exact (horig a b h _ h1).1 e
        · exact (horig a b h _ h1).2 e
      · exact h1 rfl
    · rw [hfo c hc] at hz
      rcases key a b h _ hz with h1 | ⟨-, h2, -⟩
      · exact P.interior_not_branch a b h _ h1 ⟨c, rfl⟩
      · rcases h2 with e | e
        · exact hbx c hc e
        · exact hby c e
  · intro a b h c d h' hne
    rw [Set.disjoint_left]
    intro z hz1 hz2
    rcases key a b h z hz1 with h1 | ⟨-, h2, c₁, hc₁, e₁, v₁⟩ <;>
      rcases key c d h' z hz2 with h3 | ⟨-, h4, c₂, hc₂, e₂, v₂⟩
    · exact Set.disjoint_left.1 (P.disjoint a b h c d h' hne) h1 h3
    · rcases h4 with e | e
      · exact (horig a b h z h1).1 e
      · exact (horig a b h z h1).2 e
    · rcases h2 with e | e
      · exact (horig c d h' z h3).1 e
      · exact (horig c d h' z h3).2 e
    · have := hone c₁ c₂ hc₁ hc₂ v₁ v₂
      subst this
      exact hne (e₁.trans e₂.symm)

/-- Case C: if the four paths at the branch vertex `x = P.branch a₀` split in pairs (the first
edges of `a₁`, `a₂` meet `x`, those of `b₁`, `b₂` meet `y`), there is a subdivision of `K₃,₃`.
The two sides are `{x, f b₁, f b₂}` and `{y, f a₁, f a₂}`, and the paths are `xy`, `x → f aⱼ`,
`f bᵢ → y`, and the four original paths `bᵢ — aⱼ`. -/
theorem SubdivisionPaths.containsSubdivision_K33_of_split (hxy : G.Adj x y)
    (P : SubdivisionPaths K (contractEdge G x y)) {a₀ a₁ a₂ b₁ b₂ : W} (hxa : P.branch a₀ = x)
    (hy : y ∉ Set.range P.branch)
    (ha₁ : K.Adj a₀ a₁) (ha₂ : K.Adj a₀ a₂) (hb₁ : K.Adj a₀ b₁) (hb₂ : K.Adj a₀ b₂)
    (h₁₁ : K.Adj b₁ a₁) (h₁₂ : K.Adj b₁ a₂) (h₂₁ : K.Adj b₂ a₁) (h₂₂ : K.Adj b₂ a₂)
    (hna : a₁ ≠ a₂) (hnb : b₁ ≠ b₂)
    (hxa₁ : G.Adj x (P.path a₀ a₁ ha₁).snd) (hxa₂ : G.Adj x (P.path a₀ a₂ ha₂).snd)
    (hyb₁ : G.Adj y (P.path a₀ b₁ hb₁).snd) (hyb₂ : G.Adj y (P.path a₀ b₂ hb₂).snd) :
    ContainsSubdivision G K33 := by
  classical
  have hby : ∀ a, P.branch a ≠ y := fun a e ↦ hy ⟨a, e⟩
  let wL : Fin 3 → W := ![a₀, b₁, b₂]
  let wR : Fin 3 → W := ![a₀, a₁, a₂]
  have h3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  have hwL : Function.Injective wL := by
    intro i j e
    rcases h3 i with rfl | rfl | rfl <;> rcases h3 j with rfl | rfl | rfl
    all_goals first
      | rfl
      | exact absurd e hb₁.ne
      | exact absurd e hb₂.ne
      | exact absurd e hb₁.ne.symm
      | exact absurd e hb₂.ne.symm
      | exact absurd e hnb
      | exact absurd e hnb.symm
  have hwR : Function.Injective wR := by
    intro i j e
    rcases h3 i with rfl | rfl | rfl <;> rcases h3 j with rfl | rfl | rfl
    all_goals first
      | rfl
      | exact absurd e ha₁.ne
      | exact absurd e ha₂.ne
      | exact absurd e ha₁.ne.symm
      | exact absurd e ha₂.ne.symm
      | exact absurd e hna
      | exact absurd e hna.symm
  have hwLR : ∀ i j, wL i = wR j → i = 0 ∧ j = 0 := by
    intro i j e
    rcases h3 i with rfl | rfl | rfl <;> rcases h3 j with rfl | rfl | rfl
    all_goals first
      | exact ⟨rfl, rfl⟩
      | exact absurd e ha₁.ne
      | exact absurd e ha₂.ne
      | exact absurd e hb₁.ne.symm
      | exact absurd e hb₂.ne.symm
      | exact absurd e h₁₁.ne
      | exact absurd e h₁₂.ne
      | exact absurd e h₂₁.ne
      | exact absurd e h₂₂.ne
  have hK : ∀ i j, (i, j) ≠ (0, 0) → K.Adj (wL i) (wR j) := by
    intro i j hij
    rcases h3 i with rfl | rfl | rfl <;> rcases h3 j with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hij
      | exact ha₁
      | exact ha₂
      | exact hb₁.symm
      | exact hb₂.symm
      | exact h₁₁
      | exact h₁₂
      | exact h₂₁
      | exact h₂₂
  have hK0R : ∀ j, j ≠ 0 → K.Adj a₀ (wR j) := fun j hj ↦ hK 0 j (by simp [hj])
  have hK0L : ∀ i, i ≠ 0 → K.Adj a₀ (wL i) := fun i hi ↦ (hK i 0 (by simp [hi])).symm
  have hX : ∀ j (hj : j ≠ 0), G.Adj x (P.path a₀ (wR j) (hK0R j hj)).snd := by
    intro j hj
    rcases h3 j with rfl | rfl | rfl
    · exact absurd rfl hj
    · exact hxa₁
    · exact hxa₂
  have hY : ∀ i (hi : i ≠ 0), G.Adj y (P.path a₀ (wL i) (hK0L i hi)).snd := by
    intro i hi
    rcases h3 i with rfl | rfl | rfl
    · exact absurd rfl hi
    · exact hyb₁
    · exact hyb₂
  have hbx : ∀ a, a ≠ a₀ → P.branch a ≠ x :=
    fun a ha e ↦ ha (P.branch.injective (e.trans hxa.symm))
  -- a path whose first edge meets the new branch vertex lifts without inserted vertices
  have hlift : ∀ {t : V} (ht : t = x ∨ t = y) (c : W) (h : K.Adj a₀ c),
      G.Adj t (P.path a₀ c h).snd → ∃ r : G.Walk t (P.branch c), r.IsPath ∧
        ∀ z ∈ walkInterior r, z ∈ walkInterior (P.path a₀ c h) := by
    intro t ht c h hv
    obtain ⟨r, hr, hs⟩ := exists_liftFrom hxy ht ((P.path a₀ c h).copy hxa rfl)
      ((Walk.isPath_copy _ _ _).2 (P.isPath a₀ c h)) (hbx c h.ne.symm)
    refine ⟨r, hr, fun z hz ↦ ?_⟩
    have hs' := hs z hz.1
    simp only [Walk.support_copy, Walk.getVert_copy] at hs'
    rcases hs' with e | ⟨hs₁, hs₂⟩ | ⟨-, hn⟩
    · exact absurd e hz.2.1
    · exact ⟨hs₁, by rwa [hxa], hz.2.2⟩
    · exact absurd hv hn
  have hRx : ∀ j (hj : j ≠ 0), ∃ r : G.Walk x (P.branch (wR j)), r.IsPath ∧
      ∀ z ∈ walkInterior r, z ∈ walkInterior (P.path a₀ (wR j) (hK0R j hj)) :=
    fun j hj ↦ hlift (Or.inl rfl) _ _ (hX j hj)
  have hRy : ∀ i (hi : i ≠ 0), ∃ r : G.Walk y (P.branch (wL i)), r.IsPath ∧
      ∀ z ∈ walkInterior r, z ∈ walkInterior (P.path a₀ (wL i) (hK0L i hi)) :=
    fun i hi ↦ hlift (Or.inr rfl) _ _ (hY i hi)
  choose Rx hRxp hRxi using hRx
  choose Ry hRyp hRyi using hRy
  -- branch vertices
  let Lb : Fin 3 → V := fun i ↦ P.branch (wL i)
  let Rb : Fin 3 → V := fun j ↦ if j = 0 then y else P.branch (wR j)
  have hinj : Function.Injective (Sum.elim Lb Rb) := by
    rintro (i | j) (i' | j') e
    · exact congrArg Sum.inl (hwL (P.branch.injective e))
    · simp only [Sum.elim_inl, Sum.elim_inr, Lb, Rb] at e
      split_ifs at e with hj'
      · exact absurd e (hby _)
      · exact absurd (hwLR i j' (P.branch.injective e)).2 hj'
    · simp only [Sum.elim_inl, Sum.elim_inr, Lb, Rb] at e
      split_ifs at e with hj
      · exact absurd e.symm (hby _)
      · exact absurd (hwLR i' j (P.branch.injective e.symm)).2 hj
    · simp only [Sum.elim_inr, Rb] at e
      split_ifs at e with hj hj' hj'
      · rw [hj, hj']
      · exact absurd e.symm (hby _)
      · exact absurd e (hby _)
      · exact congrArg Sum.inr (hwR (P.branch.injective e))
  let f : Fin 3 ⊕ Fin 3 ↪ V := ⟨Sum.elim Lb Rb, hinj⟩
  have hL0 : ∀ i : Fin 3, i = 0 → x = f (.inl i) := by
    rintro i rfl
    exact hxa.symm
  have hR0 : ∀ j : Fin 3, j = 0 → y = f (.inr j) := by
    rintro j rfl
    simp [f, Rb]
  have hRj : ∀ j : Fin 3, j ≠ 0 → P.branch (wR j) = f (.inr j) := by
    intro j hj
    simp [f, Rb, hj]
  have hLi : ∀ i : Fin 3, P.branch (wL i) = f (.inl i) := fun _ ↦ rfl
  -- paths
  let p : ∀ i j : Fin 3, G.Walk (f (.inl i)) (f (.inr j)) := fun i j ↦
    if hj : j = 0 then
      if hi : i = 0 then (Walk.cons hxy Walk.nil).copy (hL0 i hi) (hR0 j hj)
      else (Ry i hi).reverse.copy (hLi i) (hR0 j hj)
    else
      if hi : i = 0 then (Rx j hj).copy (hL0 i hi) (hRj j hj)
      else (liftPath hxy (P.path (wL i) (wR j) (hK i j (by simp [hi])))).copy (hLi i) (hRj j hj)
  have hxnot : ∀ i j (h : K.Adj (wL i) (wR j)), i ≠ 0 → j ≠ 0 →
      x ∉ (P.path (wL i) (wR j) h).support := by
    intro i j h hi hj hx
    have hLi : wL i ≠ a₀ := fun e ↦ hi (hwL e)
    have hRj : wR j ≠ a₀ := fun e ↦ hj (hwR e)
    exact P.interior_not_branch _ _ h x ⟨hx, (hbx _ hLi).symm, (hbx _ hRj).symm⟩ ⟨a₀, hxa⟩
  have hp0 : walkInterior (p 0 0) = ∅ := by
    simp only [p, ↓reduceDIte, walkInterior_copy, walkInterior_cons_nil]
  have hpint : ∀ i j (hij : (i, j) ≠ (0, 0)), ∀ z ∈ walkInterior (p i j),
      z ∈ walkInterior (P.path (wL i) (wR j) (hK i j hij)) := by
    intro i j hij z hz
    by_cases hj : j = 0
    · subst hj
      have hi : i ≠ 0 := fun e ↦ hij (by rw [e])
      have e : walkInterior (p i 0) = walkInterior (Ry i hi) := by
        simp only [p, hi, ↓reduceDIte]
        rw [walkInterior_copy, walkInterior_reverse]
      rw [e] at hz
      rw [← P.walkInterior_path_symm]
      exact hRyi i hi z hz
    · by_cases hi : i = 0
      · subst hi
        simp only [p, hj, ↓reduceDIte, walkInterior_copy] at hz
        exact hRxi j hj z hz
      · have e : walkInterior (p i j) =
            walkInterior (liftPath hxy (P.path (wL i) (wR j) (hK i j hij))) := by
          simp only [p, hj, hi, ↓reduceDIte]
          rw [walkInterior_copy]
        rw [e] at hz
        exact walkInterior_liftPath_subset_of_not_mem hxy _ (hxnot i j _ hi hj) hz
  have horig : ∀ a b (h : K.Adj a b), ∀ z ∈ walkInterior (P.path a b h),
      z ∉ Set.range P.branch ∧ z ≠ y :=
    fun a b h z hz ↦ ⟨P.interior_not_branch a b h z hz,
      fun e ↦ not_mem_support_contractEdge _ (hby a) (e ▸ hz.1)⟩
  refine (SubdivisionPaths.ofBipartite f p ?_ ?_ ?_).containsSubdivision_of_finite
  · intro i j
    by_cases hj : j = 0
    · by_cases hi : i = 0
      · simp only [p, hj, hi, ↓reduceDIte, Walk.isPath_copy]
        rw [Walk.cons_isPath_iff]
        exact ⟨Walk.IsPath.nil, by simpa using hxy.ne⟩
      · simp only [p, hj, hi, ↓reduceDIte, Walk.isPath_copy, Walk.isPath_reverse_iff]
        exact hRyp i hi
    · by_cases hi : i = 0
      · simp only [p, hj, hi, ↓reduceDIte, Walk.isPath_copy]
        exact hRxp j hj
      · simp only [p, hj, hi, ↓reduceDIte, Walk.isPath_copy]
        exact liftPath_isPath hxy _
  · intro i j z hz
    by_cases hij : (i, j) = (0, 0)
    · simp only [Prod.mk.injEq] at hij
      obtain ⟨rfl, rfl⟩ := hij
      rw [hp0] at hz
      exact hz.elim
    obtain ⟨hzb, hzy⟩ := horig _ _ _ z (hpint i j hij z hz)
    rintro ⟨i' | j', rfl⟩
    · exact hzb ⟨wL i', rfl⟩
    · simp only [f, Function.Embedding.coeFn_mk, Sum.elim_inr, Rb] at hzb hzy
      split_ifs at hzb hzy
      · exact hzy rfl
      · exact hzb ⟨wR j', rfl⟩
  · intro i j k l hne
    by_cases hij : (i, j) = (0, 0)
    · simp only [Prod.mk.injEq] at hij
      obtain ⟨rfl, rfl⟩ := hij
      rw [hp0]
      exact Set.empty_disjoint _
    by_cases hkl : (k, l) = (0, 0)
    · simp only [Prod.mk.injEq] at hkl
      obtain ⟨rfl, rfl⟩ := hkl
      rw [hp0]
      exact Set.disjoint_empty _
    have hs : s(wL i, wR j) ≠ s(wL k, wR l) := by
      intro e
      rcases Sym2.eq_iff.1 e with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
      · exact hne (by rw [hwL e₁, hwR e₂])
      · obtain ⟨rfl, rfl⟩ := hwLR i l e₁
        obtain ⟨rfl, rfl⟩ := hwLR k j e₂.symm
        exact hij rfl
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact Set.disjoint_left.1 (P.disjoint _ _ (hK i j hij) _ _ (hK k l hkl) hs)
      (hpint i j hij z hz1) (hpint k l hkl z hz2)

/-- If `K` has no isolated vertices, `y` is not a branch vertex of a path system in the
contracted graph. -/
theorem SubdivisionPaths.y_not_mem_range (P : SubdivisionPaths K (contractEdge G x y))
    (hK : ∀ a, ∃ c, K.Adj a c) : y ∉ Set.range P.branch := by
  rintro ⟨a, ha⟩
  obtain ⟨c, hc⟩ := hK a
  have hne : P.branch c ≠ y := fun e ↦ P.branch_ne hc (ha.trans e.symm)
  have h1 := not_mem_support_contractEdge (P.path a c hc).reverse hne
  have h2 : P.branch a ∈ (P.path a c hc).reverse.support := Walk.end_mem_support _
  generalize (P.path a c hc).reverse.support = L at h1 h2
  rw [ha] at h2
  exact h1 h2

/-- Either the path system lifts, or the paths at the branch vertex `x` split in pairs. A path
whose first edge does not meet `x` meets `y`, so the two kinds of bad paths are different. -/
theorem SubdivisionPaths.nonempty_lift_or_split [Finite W] (hxy : G.Adj x y)
    (P : SubdivisionPaths K (contractEdge G x y)) (hy : y ∉ Set.range P.branch) :
    Nonempty (SubdivisionPaths K G) ∨
      ∃ a₀ a₁ a₂ b₁ b₂, ∃ (_ : P.branch a₀ = x) (ha₁ : K.Adj a₀ a₁) (ha₂ : K.Adj a₀ a₂)
        (hb₁ : K.Adj a₀ b₁) (hb₂ : K.Adj a₀ b₂), a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧
        a₁ ≠ b₁ ∧ a₁ ≠ b₂ ∧ a₂ ≠ b₁ ∧ a₂ ≠ b₂ ∧
        G.Adj x (P.path a₀ a₁ ha₁).snd ∧ G.Adj x (P.path a₀ a₂ ha₂).snd ∧
        G.Adj y (P.path a₀ b₁ hb₁).snd ∧ G.Adj y (P.path a₀ b₂ hb₂).snd := by
  by_cases hx : x ∈ Set.range P.branch
  swap
  · exact Or.inl (P.nonempty_lift_of_not_branch hxy hx hy)
  obtain ⟨a₀, hxa⟩ := hx
  have cover : ∀ c (h : K.Adj a₀ c), G.Adj x (P.path a₀ c h).snd ∨ G.Adj y (P.path a₀ c h).snd := by
    intro c h
    have hn : ¬ (P.path a₀ c h).Nil := Walk.not_nil_of_ne (P.branch_ne h)
    have hadj := (P.path a₀ c h).adj_snd hn
    generalize (P.path a₀ c h).snd = b at hadj ⊢
    rw [hxa] at hadj
    exact adj_x_or_adj_y_of_contractEdge_adj hadj
  by_cases h1 : ∀ c c' (h : K.Adj a₀ c) (h' : K.Adj a₀ c'),
      ¬ G.Adj x (P.path a₀ c h).snd → ¬ G.Adj x (P.path a₀ c' h').snd → c = c'
  · exact Or.inl (P.nonempty_lift_of_branch hxy hxa hy (Or.inl rfl) h1)
  by_cases h2 : ∀ c c' (h : K.Adj a₀ c) (h' : K.Adj a₀ c'),
      ¬ G.Adj y (P.path a₀ c h).snd → ¬ G.Adj y (P.path a₀ c' h').snd → c = c'
  · exact Or.inl (P.nonempty_lift_of_branch hxy hxa hy (Or.inr rfl) h2)
  simp only [not_forall] at h1 h2
  obtain ⟨b₁, b₂, hb₁, hb₂, nb₁, nb₂, hb⟩ := h1
  obtain ⟨a₁, a₂, ha₁, ha₂, na₁, na₂, ha⟩ := h2
  have ab : ∀ a b (h : K.Adj a₀ a) (h' : K.Adj a₀ b), ¬ G.Adj y (P.path a₀ a h).snd →
      ¬ G.Adj x (P.path a₀ b h').snd → a ≠ b := by
    rintro a b h h' na nb rfl
    exact na ((cover a h').resolve_left nb)
  exact Or.inr ⟨a₀, a₁, a₂, b₁, b₂, hxa, ha₁, ha₂, hb₁, hb₂, ha, hb,
    ab _ _ ha₁ hb₁ na₁ nb₁, ab _ _ ha₁ hb₂ na₁ nb₂, ab _ _ ha₂ hb₁ na₂ nb₁,
    ab _ _ ha₂ hb₂ na₂ nb₂, (cover a₁ ha₁).resolve_right na₁, (cover a₂ ha₂).resolve_right na₂,
    (cover b₁ hb₁).resolve_left nb₁, (cover b₂ hb₂).resolve_left nb₂⟩

end Lift

/-! ### Lifting subdivisions of `K₅` and `K₃,₃` -/

section Final

variable {V : Type*} {G : SimpleGraph V} {x y : V}

/-- A vertex of `K₃,₃` cannot have four distinct neighbors. -/
theorem K33_not_four_neighbors {a c₁ c₂ c₃ c₄ : Fin 3 ⊕ Fin 3} (h₁ : K33.Adj a c₁)
    (h₂ : K33.Adj a c₂) (h₃ : K33.Adj a c₃) (h₄ : K33.Adj a c₄) (n₁₂ : c₁ ≠ c₂) (n₁₃ : c₁ ≠ c₃)
    (n₁₄ : c₁ ≠ c₄) (n₂₃ : c₂ ≠ c₃) (n₂₄ : c₂ ≠ c₄) (n₃₄ : c₃ ≠ c₄) : False := by
  have key : ∀ j₁ j₂ j₃ j₄ : Fin 3, j₁ ≠ j₂ → j₁ ≠ j₃ → j₁ ≠ j₄ → j₂ ≠ j₃ → j₂ ≠ j₄ →
      j₃ ≠ j₄ → False := by
    intro j₁ j₂ j₃ j₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄
    have e₁₂ : j₁.val ≠ j₂.val := fun e ↦ h₁₂ (Fin.ext e)
    have e₁₃ : j₁.val ≠ j₃.val := fun e ↦ h₁₃ (Fin.ext e)
    have e₁₄ : j₁.val ≠ j₄.val := fun e ↦ h₁₄ (Fin.ext e)
    have e₂₃ : j₂.val ≠ j₃.val := fun e ↦ h₂₃ (Fin.ext e)
    have e₂₄ : j₂.val ≠ j₄.val := fun e ↦ h₂₄ (Fin.ext e)
    have e₃₄ : j₃.val ≠ j₄.val := fun e ↦ h₃₄ (Fin.ext e)
    have := j₁.isLt
    have := j₂.isLt
    have := j₃.isLt
    have := j₄.isLt
    omega
  rcases a with i | i <;> rcases c₁ with j₁ | j₁ <;> rcases c₂ with j₂ | j₂ <;>
    rcases c₃ with j₃ | j₃ <;> rcases c₄ with j₄ | j₄
  all_goals first
    | (simp at h₁; done)
    | (simp at h₂; done)
    | (simp at h₃; done)
    | (simp at h₄; done)
    | exact key j₁ j₂ j₃ j₄ (fun e ↦ n₁₂ (by rw [e])) (fun e ↦ n₁₃ (by rw [e]))
        (fun e ↦ n₁₄ (by rw [e])) (fun e ↦ n₂₃ (by rw [e])) (fun e ↦ n₂₄ (by rw [e]))
        (fun e ↦ n₃₄ (by rw [e]))

/-- If the contracted graph contains a subdivision of `K₃,₃`, so does the original graph. -/
theorem containsSubdivision_K33_of_contractEdge (hxy : G.Adj x y)
    (h : ContainsSubdivision (contractEdge G x y) K33) : ContainsSubdivision G K33 := by
  obtain ⟨P⟩ := h.nonempty_subdivisionPaths
  have hy : y ∉ Set.range P.branch := P.y_not_mem_range (by
    rintro (i | i)
    · exact ⟨.inr 0, by simp⟩
    · exact ⟨.inl 0, by simp⟩)
  rcases P.nonempty_lift_or_split hxy hy with hP |
      ⟨a₀, a₁, a₂, b₁, b₂, -, ha₁, ha₂, hb₁, hb₂, n₁, n₂, n₃, n₄, n₅, n₆, -⟩
  · obtain ⟨P'⟩ := hP
    exact P'.containsSubdivision_of_finite
  · exact (K33_not_four_neighbors ha₁ ha₂ hb₁ hb₂ n₁ n₃ n₄ n₅ n₆ n₂).elim

/-- If the contracted graph contains a subdivision of `K₅`, the original graph contains a
subdivision of `K₅` or of `K₃,₃`. The `K₃,₃` case arises when the four paths at the branch vertex
`x` split in pairs. -/
theorem containsSubdivision_K5_or_K33_of_contractEdge (hxy : G.Adj x y)
    (h : ContainsSubdivision (contractEdge G x y) K5) :
    ContainsSubdivision G K5 ∨ ContainsSubdivision G K33 := by
  obtain ⟨P⟩ := h.nonempty_subdivisionPaths
  have hy : y ∉ Set.range P.branch := P.y_not_mem_range (fun a ↦ ⟨a + 1, by simp⟩)
  rcases P.nonempty_lift_or_split hxy hy with hP |
      ⟨a₀, a₁, a₂, b₁, b₂, hxa, ha₁, ha₂, hb₁, hb₂, n₁, n₂, n₃, n₄, n₅, n₆, hx₁, hx₂, hy₁, hy₂⟩
  · obtain ⟨P'⟩ := hP
    exact Or.inl P'.containsSubdivision_of_finite
  · refine Or.inr (P.containsSubdivision_K33_of_split hxy hxa hy ha₁ ha₂ hb₁ hb₂ ?_ ?_ ?_ ?_
      n₁ n₂ hx₁ hx₂ hy₁ hy₂)
    · exact (top_adj _ _).2 n₃.symm
    · exact (top_adj _ _).2 n₅.symm
    · exact (top_adj _ _).2 n₄.symm
    · exact (top_adj _ _).2 n₆.symm

/-- Contains no subdivision of `K₅` and no subdivision of `K₃,₃` (KF). -/
def KuratowskiFree (G : SimpleGraph V) : Prop :=
  ¬ ContainsSubdivision G K5 ∧ ¬ ContainsSubdivision G K33

/-- Blueprint `lem:lift`: if `x ∼ y` and `G` is KF, then `G/xy` is KF. -/
theorem kuratowskiFree_contractEdge (hxy : G.Adj x y) (h5 : ¬ ContainsSubdivision G K5)
    (h33 : ¬ ContainsSubdivision G K33) :
    ¬ ContainsSubdivision (contractEdge G x y) K5 ∧
      ¬ ContainsSubdivision (contractEdge G x y) K33 :=
  ⟨fun h ↦ (containsSubdivision_K5_or_K33_of_contractEdge hxy h).elim h5 h33,
    fun h ↦ h33 (containsSubdivision_K33_of_contractEdge hxy h)⟩

theorem KuratowskiFree.contractEdge (h : KuratowskiFree G) (hxy : G.Adj x y) :
    KuratowskiFree (contractEdge G x y) :=
  kuratowskiFree_contractEdge hxy h.1 h.2

end Final

end Kuratowski
