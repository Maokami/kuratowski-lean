import Kuratowski.ContractCounts
import Kuratowski.Lift

/-!
# Replacing an external path by an edge

If `H ≤ G`, `G` is Kuratowski-free, `x ≠ z`, and an `x`–`z` path in `G` has interior
outside `H.support`, then `H ⊔ edge x z` is Kuratowski-free.
Strong induction on path length contracts an internal vertex at each step.
`KuratowskiFree.contractEdge` preserves the excluded subdivisions, and the
contracted vertex is isolated in `H`, so the edges of `H` survive.
The projected tail avoids the retained vertex; `bypass` makes it a path.
No finiteness assumption is needed.
-/

namespace Kuratowski
open SimpleGraph
variable {V : Type*} {G H : SimpleGraph V} {x y : V}

/-- Project a walk avoiding `x` along `y ↦ x`. No edge collapses, so its length is unchanged. -/
noncomputable def contractAvoidWalk [DecidableEq V] (hxy : x ≠ y) {a b : V}
    (q : G.Walk a b) (hx : x ∉ q.support) :
    (contractEdge G x y).Walk (contractVertex x y a) (contractVertex x y b) := by
  induction q with
  | nil => exact .nil
  | @cons a c b hac p ih =>
    have ha : a ≠ x := fun e ↦ hx (by simp [e])
    have hc : c ≠ x := fun e ↦ hx (by
      rw [Walk.support_cons]
      exact List.mem_cons_of_mem _ (e ▸ p.start_mem_support))
    exact .cons (contractEdge_adj_contractVertex hxy ha hc hac)
      (ih (fun h ↦ hx (by simp [h])))

lemma contractAvoidWalk_length [DecidableEq V] (hxy : x ≠ y) {a b : V}
    (q : G.Walk a b) (hx : x ∉ q.support) : (contractAvoidWalk hxy q hx).length = q.length := by
  induction q with
  | nil => rfl
  | cons hac p ih => simpa [contractAvoidWalk] using ih _

lemma contractAvoidWalk_support [DecidableEq V] (hxy : x ≠ y) {a b : V}
    (q : G.Walk a b) (hx : x ∉ q.support) :
    (contractAvoidWalk hxy q hx).support = q.support.map (contractVertex x y) := by
  induction q with
  | nil => rfl
  | @cons a c b hac p ih =>
    simpa only [contractAvoidWalk, Walk.support_cons, List.map_cons] using
      congrArg (List.cons (contractVertex x y a)) (ih _)

end Kuratowski


namespace Kuratowski
open SimpleGraph
variable {V : Type*}

/-- Subgraphs of Kuratowski-free graphs are Kuratowski-free. -/
theorem KuratowskiFree.mono {G H : SimpleGraph V} (h : KuratowskiFree G) (hle : H ≤ G) :
    KuratowskiFree H := by
  constructor
  · rintro ⟨f, J, hJ, hJG⟩
    exact h.1 ⟨f, J, hJ, hJG.trans hle⟩
  · rintro ⟨f, J, hJ, hJG⟩
    exact h.2 ⟨f, J, hJ, hJG.trans hle⟩

/-- Adding an edge realized by a path whose interior avoids `H.support`
preserves Kuratowski-freeness. -/
theorem KuratowskiFree.sup_edge_of_path {G H : SimpleGraph V} (hKF : KuratowskiFree G)
    (hHG : H ≤ G) {x z : V} (hxz : x ≠ z) (p : G.Walk x z) (hp : p.IsPath)
    (havoid : ∀ u ∈ walkInterior p, H.IsIsolated u) : KuratowskiFree (H ⊔ edge x z) := by
  classical
  suffices main : ∀ n : ℕ, ∀ {G H : SimpleGraph V}, KuratowskiFree G → H ≤ G →
      ∀ {x z : V}, x ≠ z → ∀ (p : G.Walk x z), p.length = n → p.IsPath →
        (∀ u ∈ walkInterior p, H.IsIsolated u) → KuratowskiFree (H ⊔ edge x z) by
    exact main p.length hKF hHG hxz p rfl hp havoid
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G H hKF hHG x z hxz p hn hp havoid
    cases p with
    | nil => exact False.elim (hxz rfl)
    | @cons x u z hxu q =>
      have hqp := (Walk.cons_isPath_iff hxu q).1 hp
      by_cases hnil : q.Nil
      · have huz : u = z := hnil.eq
        subst z
        apply hKF.mono
        refine sup_le hHG ?_
        intro a b hab
        rcases (edge_adj x u a b).1 hab with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
        · exact hxu
        · exact hxu.symm
      have huz : u ≠ z := fun h ↦ hnil (hqp.1.nil_iff_eq.2 h)
      have hu : H.IsIsolated u := havoid u
        ⟨by simp, hxu.ne.symm, huz⟩
      have hH' : H ≤ Kuratowski.contractEdge G x u := le_contractEdge_of_isIsolated hHG hu
      let q₀ := contractAvoidWalk hxu.ne q hqp.2
      have hstart : contractVertex x u u = x := by simp [contractVertex]
      have hend : contractVertex x u z = z := by simp [contractVertex, huz.symm]
      let q' : (Kuratowski.contractEdge G x u).Walk x z := q₀.copy hstart hend
      have hlen : q'.bypass.length < n := by
        have hle := q'.length_bypass_le_length
        have heq : q'.length = q.length := by
          simp only [q', Walk.length_copy, q₀, contractAvoidWalk_length]
        simp only [Walk.length_cons] at hn
        omega
      apply ih q'.bypass.length hlen (hKF.contractEdge hxu) hH' hxz q'.bypass rfl
        q'.bypass_isPath
      intro w hw
      have hmem : w ∈ q'.support := Walk.support_bypass_subset_support q' hw.1
      rw [show q'.support = q.support.map (contractVertex x u) by
        simp only [q', Walk.support_copy, q₀, contractAvoidWalk_support]] at hmem
      obtain ⟨a, ha, haw⟩ := List.mem_map.1 hmem
      by_cases hau : a = u
      · subst a
        have : w = x := by simpa [contractVertex] using haw.symm
        exact False.elim (hw.2.1 this)
      have haw' : a = w := by simpa [contractVertex, hau] using haw
      have hai : H.IsIsolated a := havoid a
        ⟨by simp [ha], fun h ↦ hqp.2 (h ▸ ha), fun haz ↦ hw.2.2 (haw'.symm.trans haz)⟩
      exact haw' ▸ hai

end Kuratowski

