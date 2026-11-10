import Kuratowski.Paths
import Kuratowski.Subdivision

/-!
# From subdivisions to path systems (forward direction of blueprint `thm:paths_iff`)

If `IsSubdivision K f H`, then `H` contains a path system with branch vertices `f`
(`IsSubdivision.exists_subdivisionPaths`). Hence if `G` contains a subdivision of `K`, then `G`
contains a path system of `K` (`ContainsSubdivision.nonempty_subdivisionPaths`).

The proof is by induction on `IsSubdivision`. The base case is `SubdivisionPaths.ofMapLE`. In the
step that subdivides an edge `xy` by an isolated vertex `w`, the edge `xy` of each path is replaced
by `x - w - y` (`subdivideWalk`). Paths of two distinct `K`-edges cannot use the same edge `xy`
(`SubdivisionPaths.sym2_eq_of_mem_edges`), so the new vertex `w` enters the interior of the path
of at most one edge.

The reverse direction (from path systems to subdivisions) and the equivalence are in
`SubdivisionOfPaths.lean`. The equivalence assumes finite `V`; the reverse direction also has a
version for finite `W` (`exists_isSubdivision_le_of_finite`).
-/

namespace Kuratowski

open SimpleGraph

variable {V W : Type*}

/-! ### Transport to a supergraph -/

@[simp] theorem walkInterior_mapLe {H G : SimpleGraph V} (hle : H ≤ G) {u v : V}
    (p : H.Walk u v) : walkInterior (p.mapLe hle) = walkInterior p := by
  ext z
  simp [mem_walkInterior]

namespace SubdivisionPaths

variable {K : SimpleGraph W} {H G : SimpleGraph V}

/-- If `H ≤ G`, a path system in `H` is a path system in `G`. -/
def mono (P : SubdivisionPaths K H) (hle : H ≤ G) : SubdivisionPaths K G where
  branch := P.branch
  path a b h := (P.path a b h).mapLe hle
  isPath a b h := (Walk.isPath_mapLe hle).2 (P.isPath a b h)
  path_symm a b h := by rw [P.path_symm, Walk.reverse_mapLe]
  interior_not_branch a b h z hz :=
    P.interior_not_branch a b h z (by simpa using hz)
  disjoint a b h c d h' hne := by
    simpa using P.disjoint a b h c d h' hne

@[simp] theorem mono_branch (P : SubdivisionPaths K H) (hle : H ≤ G) :
    (P.mono hle).branch = P.branch := rfl

/-- Paths of two distinct `K`-edges do not use the same edge. If both use an edge `xy`, then `x`
and `y` are endpoints of both paths, and since the branch map is injective the two `K`-edges are
equal. -/
theorem sym2_eq_of_mem_edges (P : SubdivisionPaths K H) {a b c d : W} (h : K.Adj a b)
    (h' : K.Adj c d) {x y : V} (hxy : x ≠ y) (h1 : s(x, y) ∈ (P.path a b h).edges)
    (h2 : s(x, y) ∈ (P.path c d h').edges) : s(a, b) = s(c, d) := by
  by_contra hne
  -- A vertex on both paths is in neither interior, so it is an endpoint of both paths.
  have key : ∀ z, z ∈ (P.path a b h).support → z ∈ (P.path c d h').support →
      (z = P.branch a ∨ z = P.branch b) ∧ (z = P.branch c ∨ z = P.branch d) := by
    intro z hz1 hz2
    have hn1 : z ∉ walkInterior (P.path a b h) := by
      intro hi1
      have hn2 : z ∉ walkInterior (P.path c d h') :=
        fun hi2 ↦ Set.disjoint_left.1 (P.disjoint a b h c d h' hne) hi1 hi2
      have hzc : z = P.branch c ∨ z = P.branch d := by
        by_contra hz
        exact hn2 ⟨hz2, fun e ↦ hz (Or.inl e), fun e ↦ hz (Or.inr e)⟩
      exact P.interior_not_branch a b h z hi1
        (hzc.elim (fun e ↦ ⟨c, e.symm⟩) (fun e ↦ ⟨d, e.symm⟩))
    have hn2 : z ∉ walkInterior (P.path c d h') := by
      intro hi2
      have hza : z = P.branch a ∨ z = P.branch b := by
        by_contra hz
        exact hn1 ⟨hz1, fun e ↦ hz (Or.inl e), fun e ↦ hz (Or.inr e)⟩
      exact P.interior_not_branch c d h' z hi2
        (hza.elim (fun e ↦ ⟨a, e.symm⟩) (fun e ↦ ⟨b, e.symm⟩))
    constructor
    · by_contra hz
      exact hn1 ⟨hz1, fun e ↦ hz (Or.inl e), fun e ↦ hz (Or.inr e)⟩
    · by_contra hz
      exact hn2 ⟨hz2, fun e ↦ hz (Or.inl e), fun e ↦ hz (Or.inr e)⟩
  obtain ⟨hxab, hxcd⟩ := key x (Walk.fst_mem_support_of_mem_edges _ h1)
    (Walk.fst_mem_support_of_mem_edges _ h2)
  obtain ⟨hyab, hycd⟩ := key y (Walk.snd_mem_support_of_mem_edges _ h1)
    (Walk.snd_mem_support_of_mem_edges _ h2)
  -- `{x, y}` equals the pair of branch vertices of both edges.
  have hab : s(x, y) = s(P.branch a, P.branch b) := by
    rcases hxab with rfl | rfl <;> rcases hyab with rfl | rfl
    · exact absurd rfl hxy
    · rfl
    · exact Sym2.eq_swap
    · exact absurd rfl hxy
  have hcd : s(x, y) = s(P.branch c, P.branch d) := by
    rcases hxcd with rfl | rfl <;> rcases hycd with rfl | rfl
    · exact absurd rfl hxy
    · rfl
    · exact Sym2.eq_swap
    · exact absurd rfl hxy
  apply hne
  rcases Sym2.eq_iff.1 (hab.symm.trans hcd) with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [P.branch.injective e1, P.branch.injective e2]
  · rw [P.branch.injective e1, P.branch.injective e2]
    exact Sym2.eq_swap

end SubdivisionPaths

/-! ### Transporting walks to the graph with one edge subdivided -/

section Subdivide

variable {H : SimpleGraph V} {x y w : V}

/-- An isolated vertex `w` does not occur in a walk that does not start at `w`. -/
theorem not_mem_support_of_isIsolated (hw : H.IsIsolated w) :
    ∀ {u v : V} (p : H.Walk u v), u ≠ w → w ∉ p.support
  | _, _, .nil, hu => by simpa using hu.symm
  | _, _, .cons h p, hu => by
    rw [Walk.support_cons, List.mem_cons, not_or]
    exact ⟨hu.symm, not_mem_support_of_isIsolated hw p (fun e ↦ hw _ (e ▸ h.symm))⟩

theorem adj_subdivideEdge_of_ne (hxy : H.Adj x y) (hw : H.IsIsolated w) {u b : V}
    (h : H.Adj u b) (he : s(u, b) ≠ s(x, y)) : (subdivideEdge H x y w).Adj u b := by
  obtain ⟨hxw, hwy⟩ := ne_of_subdivide hxy hw
  exact (subdivideEdge_adj hxw hwy).2 (Or.inl ⟨h, he⟩)

theorem adj_subdivideEdge_mid (hxy : H.Adj x y) (hw : H.IsIsolated w) {u : V}
    (hu : u = x ∨ u = y) : (subdivideEdge H x y w).Adj u w := by
  obtain ⟨hxw, hwy⟩ := ne_of_subdivide hxy hw
  rw [subdivideEdge_adj hxw hwy]
  rcases hu with rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr Sym2.eq_swap)

theorem mem_pair_of_sym2_eq {u b : V} (he : s(u, b) = s(x, y)) :
    (u = x ∨ u = y) ∧ (b = x ∨ b = y) := by
  rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨Or.inl h1, Or.inr h2⟩
  · exact ⟨Or.inr h1, Or.inl h2⟩

variable [DecidableEq V]

/-- Replace each traversal of the edge `xy` (in either direction) by `x - w - y`, giving a walk
in `subdivideEdge H x y w`. -/
def subdivideWalk (hxy : H.Adj x y) (hw : H.IsIsolated w) :
    ∀ {u v : V}, H.Walk u v → (subdivideEdge H x y w).Walk u v
  | _, _, .nil => .nil
  | _, _, @Walk.cons _ _ u b _ h p =>
    if he : s(u, b) = s(x, y) then
      .cons (adj_subdivideEdge_mid hxy hw (mem_pair_of_sym2_eq he).1)
        (.cons (adj_subdivideEdge_mid hxy hw (mem_pair_of_sym2_eq he).2).symm
          (subdivideWalk hxy hw p))
    else .cons (adj_subdivideEdge_of_ne hxy hw h he) (subdivideWalk hxy hw p)

variable (hxy : H.Adj x y) (hw : H.IsIsolated w)

theorem mem_support_subdivideWalk {u v : V} (p : H.Walk u v) (z : V) :
    z ∈ (subdivideWalk hxy hw p).support ↔ z ∈ p.support ∨ (z = w ∧ s(x, y) ∈ p.edges) := by
  induction p with
  | nil => simp [subdivideWalk]
  | @cons u b v h p ih =>
    by_cases he : s(u, b) = s(x, y)
    · simp only [subdivideWalk, he, dite_true, Walk.support_cons, List.mem_cons, ih,
        Walk.edges_cons, true_or, and_true]
      tauto
    · simp only [subdivideWalk, he, dite_false, Walk.support_cons, List.mem_cons, ih,
        Walk.edges_cons]
      constructor
      · rintro (h1 | h1 | ⟨h1, h2⟩)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h1)
        · exact Or.inr ⟨h1, Or.inr h2⟩
      · rintro ((h1 | h1) | ⟨h1, h2 | h2⟩)
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · exact absurd h2.symm he
        · exact Or.inr (Or.inr ⟨h1, h2⟩)

theorem isPath_subdivideWalk {u v : V} (p : H.Walk u v) (hp : p.IsPath) (hwp : w ∉ p.support) :
    (subdivideWalk hxy hw p).IsPath := by
  induction p with
  | nil => simp [subdivideWalk]
  | @cons u b v h p ih =>
    rw [Walk.cons_isPath_iff] at hp
    have hwp' : w ∉ p.support := fun hm ↦ hwp (by simp [hm])
    have huw : u ≠ w := fun e ↦ hwp (by simp [e])
    have hq := ih hp.1 hwp'
    by_cases he : s(u, b) = s(x, y)
    · have hnodup := (Walk.cons_isPath_iff h p).2 hp |>.isTrail.edges_nodup
      rw [Walk.edges_cons, List.nodup_cons] at hnodup
      have hxyp : s(x, y) ∉ p.edges := he ▸ hnodup.1
      have hux : u = x ∨ u = y := (mem_pair_of_sym2_eq he).1
      simp only [subdivideWalk, he, dite_true]
      rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
      refine ⟨⟨hq, ?_⟩, ?_⟩
      · rw [mem_support_subdivideWalk]
        rintro (hm | ⟨-, hm⟩)
        · exact hwp' hm
        · exact hxyp hm
      · rw [Walk.support_cons, List.mem_cons, mem_support_subdivideWalk]
        rintro (hm | hm | ⟨hm, -⟩)
        · exact huw hm
        · exact hp.2 hm
        · exact huw hm
    · simp only [subdivideWalk, he, dite_false]
      rw [Walk.cons_isPath_iff]
      refine ⟨hq, ?_⟩
      rw [mem_support_subdivideWalk]
      rintro (hm | ⟨hm, -⟩)
      · exact hp.2 hm
      · exact huw hm

theorem subdivideWalk_append {u v t : V} (p : H.Walk u v) (q : H.Walk v t) :
    subdivideWalk hxy hw (p.append q) =
      (subdivideWalk hxy hw p).append (subdivideWalk hxy hw q) := by
  induction p with
  | nil => rfl
  | @cons u b v h p ih =>
    by_cases he : s(u, b) = s(x, y)
    · simp [subdivideWalk, he, ih]
    · simp [subdivideWalk, he, ih]

theorem subdivideWalk_reverse {u v : V} (p : H.Walk u v) :
    subdivideWalk hxy hw p.reverse = (subdivideWalk hxy hw p).reverse := by
  induction p with
  | nil => rfl
  | @cons u b v h p ih =>
    rw [Walk.reverse_cons, subdivideWalk_append, ih]
    by_cases he : s(u, b) = s(x, y)
    · have he' : s(b, u) = s(x, y) := Sym2.eq_swap.trans he
      simp only [subdivideWalk, he, he', dite_true, Walk.reverse_cons]
      rw [← Walk.append_assoc]
      rfl
    · have he' : s(b, u) ≠ s(x, y) := fun e ↦ he (Sym2.eq_swap.trans e)
      simp [subdivideWalk, he, he']

/-- If the endpoints are not `w`, the interior is the original interior, plus `w` if the walk
uses the edge `xy`. -/
theorem mem_walkInterior_subdivideWalk {u v : V} (p : H.Walk u v) (hwp : w ∉ p.support) (z : V) :
    z ∈ walkInterior (subdivideWalk hxy hw p) ↔
      z ∈ walkInterior p ∨ (z = w ∧ s(x, y) ∈ p.edges) := by
  have hu : u ≠ w := fun e ↦ hwp (e ▸ p.start_mem_support)
  have hv : v ≠ w := fun e ↦ hwp (e ▸ p.end_mem_support)
  simp only [mem_walkInterior, mem_support_subdivideWalk]
  constructor
  · rintro ⟨h1 | h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr h1
  · rintro (⟨h1, h2, h3⟩ | ⟨rfl, h1⟩)
    · exact ⟨Or.inl h1, h2, h3⟩
    · exact ⟨Or.inr ⟨rfl, h1⟩, hu.symm, hv.symm⟩

end Subdivide

/-! ### Subdividing a path system -/

namespace SubdivisionPaths

variable {K : SimpleGraph W} {H : SimpleGraph V} {x y w : V} [DecidableEq V]

omit [DecidableEq V] in
theorem not_mem_support_path (P : SubdivisionPaths K H) (hw : H.IsIsolated w)
    (hwf : w ∉ Set.range P.branch) {a b : W} (h : K.Adj a b) : w ∉ (P.path a b h).support :=
  not_mem_support_of_isIsolated hw _ (fun e ↦ hwf ⟨a, e⟩)

/-- The path system in the graph obtained by subdividing `xy` with an isolated vertex `w` that is
not a branch vertex. The branch vertices are unchanged. -/
def subdivide (P : SubdivisionPaths K H) (hxy : H.Adj x y) (hwf : w ∉ Set.range P.branch)
    (hw : H.IsIsolated w) : SubdivisionPaths K (subdivideEdge H x y w) where
  branch := P.branch
  path a b h := subdivideWalk hxy hw (P.path a b h)
  isPath a b h :=
    isPath_subdivideWalk hxy hw _ (P.isPath a b h) (P.not_mem_support_path hw hwf h)
  path_symm a b h := by rw [P.path_symm, subdivideWalk_reverse]
  interior_not_branch a b h z hz := by
    rcases (mem_walkInterior_subdivideWalk hxy hw _ (P.not_mem_support_path hw hwf h) z).1 hz
      with hz | ⟨rfl, -⟩
    · exact P.interior_not_branch a b h z hz
    · exact hwf
  disjoint a b h c d h' hne := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    rcases (mem_walkInterior_subdivideWalk hxy hw _ (P.not_mem_support_path hw hwf h) z).1 hz1
      with hz1 | ⟨rfl, he1⟩ <;>
    rcases (mem_walkInterior_subdivideWalk hxy hw _ (P.not_mem_support_path hw hwf h') z).1 hz2
      with hz2 | ⟨hzw, he2⟩
    · exact Set.disjoint_left.1 (P.disjoint a b h c d h' hne) hz1 hz2
    · exact P.not_mem_support_path hw hwf h (hzw ▸ hz1.1)
    · exact P.not_mem_support_path hw hwf h' hz2.1
    · exact hne (P.sym2_eq_of_mem_edges h h' hxy.ne he1 he2)

@[simp] theorem subdivide_branch (P : SubdivisionPaths K H) (hxy : H.Adj x y)
    (hwf : w ∉ Set.range P.branch) (hw : H.IsIsolated w) :
    (P.subdivide hxy hwf hw).branch = P.branch := rfl

end SubdivisionPaths

/-! ### Forward direction -/

/-- A subdivision `H` with branch vertices `f` contains a path system of `K` with branch
vertices `f`. -/
theorem IsSubdivision.exists_subdivisionPaths {K : SimpleGraph W} {f : W ↪ V} {H : SimpleGraph V}
    (hS : IsSubdivision K f H) : ∃ P : SubdivisionPaths K H, P.branch = f := by
  classical
  induction hS with
  | map => exact ⟨SubdivisionPaths.ofMapLE _ le_rfl, rfl⟩
  | subdivide _ hxy hwf hw ih =>
    obtain ⟨P, rfl⟩ := ih
    exact ⟨P.subdivide hxy hwf hw, rfl⟩

/-- If `G` contains a subdivision of `K`, then `G` contains a path system of `K` (forward
direction of `thm:paths_iff`). -/
theorem ContainsSubdivision.nonempty_subdivisionPaths {G : SimpleGraph V} {K : SimpleGraph W}
    (h : ContainsSubdivision G K) : Nonempty (SubdivisionPaths K G) := by
  obtain ⟨f, H, hS, hle⟩ := h
  obtain ⟨P, -⟩ := hS.exists_subdivisionPaths
  exact ⟨P.mono hle⟩

end Kuratowski
