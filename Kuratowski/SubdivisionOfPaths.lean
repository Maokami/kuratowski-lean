import Kuratowski.PathsSubdivision

/-!
# 경로 체계에서 세분으로 (블루프린트 `thm:paths_iff`의 역방향과 동치)

꼭짓점 타입 `V`가 유한하면 `G` 안의 경로 체계 `P`는 분기점 배치가 `P.branch`인 `K`의 세분
`H ≤ G`를 준다 (`SubdivisionPaths.exists_isSubdivision_le`). 정방향(`PathsSubdivision.lean`)과 합치면
`containsSubdivision_iff_paths`다.

증명은 `K.map P.branch`에서 시작해 `K`의 변을 하나씩 그 경로로 바꾼다. 중간 그래프
`P.partialGraph S`는 `S`에 든 변은 경로로, 나머지 변은 두 분기점을 잇는 변으로 둔다. 경로 하나를 넣는
단계는 경로의 내부점마다 `IsSubdivision.subdivide`를 한 번씩 적용하는 것이다
(`IsSubdivision.insertPath`). 아직 넣지 않은 경로의 내부점은 경로 체계의 서로소 조건 때문에 고립점이고,
두 분기점을 잇는 변은 그 변 자신의 경로에만 나타난다 (`SubdivisionPaths.sym2_eq_of_branch_mem_edges`).

유한성은 변을 유한 번만 바꾸기 위해 필요하다. `IsSubdivision`은 유한 번의 세분만 허용한다.
-/

namespace Kuratowski

open SimpleGraph

variable {V W : Type*}

/-! ### 걸음의 변으로 이루어진 그래프 -/

/-- 걸음이 지나는 변들로 이루어진 그래프. -/
def walkGraph {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : SimpleGraph V :=
  fromEdgeSet {e | e ∈ p.edges}

theorem walkGraph_adj {G : SimpleGraph V} {u v : V} (p : G.Walk u v) {a c : V} :
    (walkGraph p).Adj a c ↔ s(a, c) ∈ p.edges ∧ a ≠ c := by
  unfold walkGraph
  exact fromEdgeSet_adj _

theorem walkGraph_cons {G : SimpleGraph V} {u b v : V} (h : G.Adj u b) (q : G.Walk b v) :
    walkGraph (Walk.cons h q) = edge u b ⊔ walkGraph q := by
  ext a c
  simp only [walkGraph_adj, Walk.edges_cons, List.mem_cons, sup_adj, edge_adj, Sym2.eq_iff]
  tauto

theorem walkGraph_le {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : walkGraph p ≤ G := by
  intro a c h
  exact p.edges_subset_edgeSet ((walkGraph_adj p).1 h).1

/-! ### 경로 하나 넣기 -/

/-- 변 하나짜리 경로를 넣으면 그래프는 그대로다. -/
theorem deleteEdges_sup_walkGraph_single {H G' : SimpleGraph V} {u b : V} (huv : H.Adj u b)
    (h : G'.Adj u b) : H.deleteEdges {s(u, b)} ⊔ walkGraph (Walk.cons h Walk.nil) = H := by
  ext a c
  simp only [sup_adj, deleteEdges_adj, Set.mem_singleton_iff, walkGraph_adj, Walk.edges_cons,
    Walk.edges_nil, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (⟨hac, -⟩ | ⟨he, -⟩)
    · exact hac
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv
      · exact huv.symm
  · intro hac
    by_cases he : s(a, c) = s(u, b)
    · exact Or.inr ⟨he, hac.ne⟩
    · exact Or.inl ⟨hac, he⟩

/-- 한 단계: `u - b - (나머지)`에서 `b`로 변 `uv`를 나눈 뒤 나머지를 넣은 그래프는, 처음부터
`u - b - (나머지)`를 넣은 그래프와 같다. -/
theorem subdivideEdge_insert_eq {H : SimpleGraph V} {u b v : V} (hb : H.IsIsolated b)
    (hub : u ≠ b) (hbv : b ≠ v) (huv : u ≠ v) (R : SimpleGraph V) :
    (subdivideEdge H u v b).deleteEdges {s(b, v)} ⊔ R =
      H.deleteEdges {s(u, v)} ⊔ (edge u b ⊔ R) := by
  ext a c
  simp only [sup_adj, deleteEdges_adj, Set.mem_singleton_iff, subdivideEdge_adj hub hbv, edge_adj]
  have hnb : ∀ {a c : V}, H.Adj a c → a ≠ b ∧ c ≠ b := by
    intro a c hac
    exact ⟨fun e ↦ hb c (e ▸ hac), fun e ↦ hb a (e ▸ hac.symm)⟩
  constructor
  · rintro (⟨(⟨hac, hne⟩ | he | he), hne'⟩ | hR)
    · exact Or.inl ⟨hac, hne⟩
    · refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
      · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hub
        · exact hub.symm
    · exact absurd he hne'
    · exact Or.inr (Or.inr hR)
  · rintro (⟨hac, hne⟩ | ⟨hu, hac⟩ | hR)
    · refine Or.inl ⟨Or.inl ⟨hac, hne⟩, ?_⟩
      intro he
      rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact (hnb hac).1 h1
      · exact (hnb hac).2 h2
    · refine Or.inl ⟨Or.inr (Or.inl ?_), ?_⟩
      · rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
      · intro he
        rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hub (h1.trans rfl ▸ rfl)
          · exact huv h1
        · rcases Sym2.eq_iff.1 he with ⟨-, h2⟩ | ⟨-, h2⟩
          · exact huv h2
          · exact hub (h2 ▸ rfl)
    · exact Or.inr hR

/-- 세분 그래프 `H`의 변 `uv`를, `H`에서 고립되어 있고 분기점이 아닌 내부점들을 지나는 경로 `p`로
바꿔도 세분이다. -/
theorem IsSubdivision.insertPath {K : SimpleGraph W} {f : W ↪ V} {G' : SimpleGraph V} :
    ∀ {u v : V} (p : G'.Walk u v) {H : SimpleGraph V}, IsSubdivision K f H → p.IsPath →
      H.Adj u v → (∀ z ∈ walkInterior p, H.IsIsolated z ∧ z ∉ Set.range f) →
      IsSubdivision K f (H.deleteEdges {s(u, v)} ⊔ walkGraph p)
  | _, _, .nil, H, _, _, huv, _ => (H.loopless.irrefl _ huv).elim
  | _, _, @Walk.cons _ _ u b _ h .nil, H, hS, _, huv, _ => by
    rw [deleteEdges_sup_walkGraph_single huv h]
    exact hS
  | _, _, @Walk.cons _ _ u b v h (@Walk.cons _ _ _ c _ h2 q), H, hS, hp, huv, hint => by
    rw [Walk.cons_isPath_iff] at hp
    have hq : (Walk.cons h2 q).IsPath := hp.1
    have hu : u ∉ (Walk.cons h2 q).support := hp.2
    rw [Walk.cons_isPath_iff] at hq
    have hub : u ≠ b := fun e ↦ hu (by simp [e])
    have hbv : b ≠ v := fun e ↦ hq.2 (e ▸ q.end_mem_support)
    have huv' : u ≠ v := fun e ↦ hu (e ▸ (Walk.cons h2 q).end_mem_support)
    have hbint : b ∈ walkInterior (Walk.cons h (Walk.cons h2 q)) :=
      ⟨by simp, hub.symm, hbv⟩
    obtain ⟨hb, hbf⟩ := hint b hbint
    have hS1 := hS.subdivide huv hbf hb
    obtain ⟨hxw, hwy⟩ := ne_of_subdivide huv hb
    have hadj1 : (subdivideEdge H u v b).Adj b v :=
      (subdivideEdge_adj hxw hwy).2 (Or.inr (Or.inr rfl))
    have hint1 : ∀ z ∈ walkInterior (Walk.cons h2 q),
        (subdivideEdge H u v b).IsIsolated z ∧ z ∉ Set.range f := by
      intro z hz
      have hzu : z ≠ u := fun e ↦ hu (e ▸ hz.1)
      have hzs : z ∈ (Walk.cons h (Walk.cons h2 q)).support := by
        rw [Walk.support_cons]
        exact List.mem_cons_of_mem _ hz.1
      obtain ⟨hzi, hzf⟩ := hint z ⟨hzs, hzu, hz.2.2⟩
      refine ⟨fun t ht ↦ ?_, hzf⟩
      rw [subdivideEdge_adj hxw hwy] at ht
      rcases ht with ⟨hzt, -⟩ | he | he
      · exact hzi t hzt
      · rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hzu h1
        · exact hz.2.1 h1
      · rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hz.2.1 h1
        · exact hz.2.2 h1
    have ih := IsSubdivision.insertPath (Walk.cons h2 q) hS1
      ((Walk.cons_isPath_iff h2 q).2 hq) hadj1 hint1
    rw [subdivideEdge_insert_eq hb hub hbv huv'] at ih
    rwa [walkGraph_cons]

/-! ### 경로 체계 전체 넣기 -/

namespace SubdivisionPaths

variable {K : SimpleGraph W} {G : SimpleGraph V}

/-- 경로 위의 분기점은 그 경로의 끝점이다. -/
theorem eq_or_eq_of_branch_mem_support (P : SubdivisionPaths K G) {a b c : W} (h : K.Adj a b)
    (hc : P.branch c ∈ (P.path a b h).support) : c = a ∨ c = b := by
  by_contra hne
  exact P.interior_not_branch a b h _
    ⟨hc, fun e ↦ hne (Or.inl (P.branch.injective e)),
      fun e ↦ hne (Or.inr (P.branch.injective e))⟩ ⟨c, rfl⟩

/-- 두 분기점 `branch a`, `branch b`를 잇는 변을 지나는 경로는 변 `ab`의 경로뿐이다. -/
theorem sym2_eq_of_branch_mem_edges (P : SubdivisionPaths K G) {a b c d : W} (h : K.Adj c d)
    (hab : a ≠ b) (he : s(P.branch a, P.branch b) ∈ (P.path c d h).edges) :
    s(a, b) = s(c, d) := by
  have ha := P.eq_or_eq_of_branch_mem_support h (Walk.fst_mem_support_of_mem_edges _ he)
  have hb := P.eq_or_eq_of_branch_mem_support h (Walk.snd_mem_support_of_mem_edges _ he)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · rfl
  · exact Sym2.eq_swap
  · exact absurd rfl hab

/-- 분기점의 쌍이 같으면 원래 꼭짓점의 쌍도 같다. -/
theorem sym2_eq_of_branch_eq (P : SubdivisionPaths K G) {a b c d : W}
    (e : s(P.branch c, P.branch d) = s(P.branch a, P.branch b)) : s(c, d) = s(a, b) := by
  rcases Sym2.eq_iff.1 e with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [P.branch.injective e1, P.branch.injective e2]
  · rw [P.branch.injective e1, P.branch.injective e2]
    exact Sym2.eq_swap

/-- 같은 무향 변의 두 경로는 같은 변을 지난다. -/
theorem mem_edges_path_of_sym2_eq (P : SubdivisionPaths K G) {a b c d : W} (h : K.Adj a b)
    (h' : K.Adj c d) (hcd : s(c, d) = s(a, b)) {t : Sym2 V} (ht : t ∈ (P.path c d h').edges) :
    t ∈ (P.path a b h).edges := by
  rcases Sym2.eq_iff.1 hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ht
  · rw [P.path_symm _ _ h, Walk.edges_reverse, List.mem_reverse] at ht
    exact ht

/-- 변 집합 `S`에 든 `K`의 변은 경로로, 나머지 변은 두 분기점을 잇는 변으로 둔 그래프. -/
def partialGraph (P : SubdivisionPaths K G) (S : Set (Sym2 W)) : SimpleGraph V :=
  fromEdgeSet ({t | ∃ a b, K.Adj a b ∧ s(a, b) ∉ S ∧ t = s(P.branch a, P.branch b)} ∪
    {t | ∃ a b, ∃ h : K.Adj a b, s(a, b) ∈ S ∧ t ∈ (P.path a b h).edges})

theorem partialGraph_empty (P : SubdivisionPaths K G) : P.partialGraph ∅ = K.map P.branch := by
  ext x y
  rw [partialGraph, fromEdgeSet_adj, map_adj]
  constructor
  · rintro ⟨(⟨a, b, h, -, he⟩ | ⟨a, b, h, ha, -⟩), -⟩
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a, b, h, rfl, rfl⟩
      · exact ⟨b, a, h.symm, rfl, rfl⟩
    · exact ((Set.mem_empty_iff_false _).1 ha).elim
  · rintro ⟨a, b, h, rfl, rfl⟩
    exact ⟨Or.inl ⟨a, b, h, fun h0 ↦ h0, rfl⟩, P.branch_ne h⟩

theorem partialGraph_adj_branch (P : SubdivisionPaths K G) {S : Set (Sym2 W)} {a b : W}
    (h : K.Adj a b) (hS : s(a, b) ∉ S) : (P.partialGraph S).Adj (P.branch a) (P.branch b) := by
  rw [partialGraph, fromEdgeSet_adj]
  exact ⟨Or.inl ⟨a, b, h, hS, rfl⟩, P.branch_ne h⟩

/-- 아직 넣지 않은 변의 경로의 내부점은 고립점이다. -/
theorem isIsolated_partialGraph (P : SubdivisionPaths K G) {S : Set (Sym2 W)} {a b : W}
    (h : K.Adj a b) (hS : s(a, b) ∉ S) {z : V} (hz : z ∈ walkInterior (P.path a b h)) :
    (P.partialGraph S).IsIsolated z := by
  have hzb := P.interior_not_branch a b h z hz
  refine fun t ht ↦ ?_
  rw [partialGraph, fromEdgeSet_adj] at ht
  rcases ht.1 with ⟨c, d, -, -, he⟩ | ⟨c, d, h', hcd, he⟩
  · rcases Sym2.eq_iff.1 he with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hzb ⟨c, rfl⟩
    · exact hzb ⟨d, rfl⟩
  · have hz' : z ∈ walkInterior (P.path c d h') :=
      ⟨Walk.fst_mem_support_of_mem_edges _ he, fun e ↦ hzb ⟨c, e.symm⟩,
        fun e ↦ hzb ⟨d, e.symm⟩⟩
    have hne : s(a, b) ≠ s(c, d) := fun e ↦ hS (by rw [e]; exact hcd)
    exact Set.disjoint_left.1 (P.disjoint a b h c d h' hne) hz hz'

/-- 변 `ab`를 하나 더 넣은 그래프는 분기점 사이의 변을 그 경로로 바꾼 그래프다. -/
theorem partialGraph_insert (P : SubdivisionPaths K G) {S : Set (Sym2 W)} {a b : W}
    (h : K.Adj a b) (hS : s(a, b) ∉ S) :
    P.partialGraph (insert s(a, b) S) =
      (P.partialGraph S).deleteEdges {s(P.branch a, P.branch b)} ⊔ walkGraph (P.path a b h) := by
  ext x y
  simp only [partialGraph, sup_adj, deleteEdges_adj, walkGraph_adj, fromEdgeSet_adj,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨(⟨c, d, h', hcd, he⟩ | ⟨c, d, h', hcd, he⟩), hxy⟩
    · rw [Set.mem_insert_iff, not_or] at hcd
      refine Or.inl ⟨⟨Or.inl ⟨c, d, h', hcd.2, he⟩, hxy⟩, ?_⟩
      rw [he]
      exact fun e ↦ hcd.1 (P.sym2_eq_of_branch_eq e)
    · rw [Set.mem_insert_iff] at hcd
      rcases hcd with hcd | hcd
      · exact Or.inr ⟨P.mem_edges_path_of_sym2_eq h h' hcd he, hxy⟩
      · refine Or.inl ⟨⟨Or.inr ⟨c, d, h', hcd, he⟩, hxy⟩, ?_⟩
        intro e
        rw [e] at he
        have := P.sym2_eq_of_branch_mem_edges h' h.ne he
        exact hS (by rw [this]; exact hcd)
  · rintro (⟨⟨(⟨c, d, h', hcd, he⟩ | ⟨c, d, h', hcd, he⟩), hxy⟩, hne⟩ | ⟨he, hxy⟩)
    · refine ⟨Or.inl ⟨c, d, h', ?_, he⟩, hxy⟩
      rw [Set.mem_insert_iff, not_or]
      refine ⟨fun e ↦ hne ?_, hcd⟩
      rw [he]
      rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
    · exact ⟨Or.inr ⟨c, d, h', Set.mem_insert_of_mem _ hcd, he⟩, hxy⟩
    · exact ⟨Or.inr ⟨a, b, h, Set.mem_insert _ _, he⟩, hxy⟩

/-- 유한한 변 집합의 경로를 모두 넣은 그래프는 세분이다. -/
theorem isSubdivision_partialGraph (P : SubdivisionPaths K G) (T : Finset (Sym2 W))
    (hT : (T : Set (Sym2 W)) ⊆ K.edgeSet) : IsSubdivision K P.branch (P.partialGraph T) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, partialGraph_empty]
    exact IsSubdivision.map _
  | @insert e T heT ih =>
    rw [Finset.coe_insert] at hT ⊢
    have ih := ih (fun t ht ↦ hT (Set.mem_insert_of_mem _ ht))
    induction e using Sym2.ind with
    | h a b =>
      have h : K.Adj a b := hT (Set.mem_insert _ _)
      have hS : s(a, b) ∉ (T : Set (Sym2 W)) := by simpa using heT
      rw [P.partialGraph_insert h hS]
      exact IsSubdivision.insertPath (P.path a b h) ih (P.isPath a b h)
        (P.partialGraph_adj_branch h hS)
        (fun z hz ↦ ⟨P.isIsolated_partialGraph h hS hz, P.interior_not_branch a b h z hz⟩)

/-- `exists_isSubdivision_le`에서 `V` 대신 `W`의 유한성만 가정한 판. -/
theorem exists_isSubdivision_le_of_finite [Finite W] (P : SubdivisionPaths K G) :
    ∃ H, IsSubdivision K P.branch H ∧ H ≤ G := by
  classical
  have : Fintype W := Fintype.ofFinite W
  have hfin : K.edgeSet.Finite := Set.toFinite _
  refine ⟨P.partialGraph hfin.toFinset, P.isSubdivision_partialGraph _ (by simp), ?_⟩
  rw [Set.Finite.coe_toFinset]
  intro x y hxy
  rw [partialGraph, fromEdgeSet_adj] at hxy
  rcases hxy.1 with ⟨c, d, h', hcd, -⟩ | ⟨c, d, h', -, he⟩
  · exact (hcd h').elim
  · exact (P.path c d h').edges_subset_edgeSet he

/-- 유한 그래프 안의 경로 체계는 같은 분기점 배치의 세분을 준다. -/
theorem exists_isSubdivision_le [Finite V] (P : SubdivisionPaths K G) :
    ∃ H, IsSubdivision K P.branch H ∧ H ≤ G := by
  have : Finite W := Finite.of_injective P.branch P.branch.injective
  exact P.exists_isSubdivision_le_of_finite

theorem containsSubdivision [Finite V] (P : SubdivisionPaths K G) : ContainsSubdivision G K := by
  obtain ⟨H, hS, hle⟩ := P.exists_isSubdivision_le
  exact ⟨P.branch, H, hS, hle⟩

end SubdivisionPaths

/-- 블루프린트 `thm:paths_iff`: 유한 그래프 `G`가 `K`의 세분을 포함하는 것은 `G` 안에 `K`의 경로
체계가 있는 것과 같다. -/
theorem containsSubdivision_iff_paths [Finite V] {G : SimpleGraph V} {K : SimpleGraph W} :
    ContainsSubdivision G K ↔ Nonempty (SubdivisionPaths K G) :=
  ⟨ContainsSubdivision.nonempty_subdivisionPaths, fun ⟨P⟩ ↦ P.containsSubdivision⟩

end Kuratowski
