import Kuratowski.ContractCounts
import Kuratowski.Lift

/-!
# 지지 집합 바깥 경로를 한 변으로 바꾸기

KF 그래프의 부분 그래프 `H`에서 `x`, `z`를 잇는 원래 그래프의 경로가 있고, 그 내부가 `H`의 고립점들로만
이루어지면 `H ⊔ edge x z`도 KF다. 경로 길이에 대한 강한 귀납법으로 내부점을 차례로 수축한다.
`KuratowskiFree.contractEdge`가 KF를 보존하고, 수축할 내부점이 `H`의 고립점이라 `H`의 변도 남는다.
걸음은 남긴 점을 피하는 꼬리만 사영해 길이를 보존한 뒤 `bypass`로 단순 경로로 줄인다.
유한성은 가정하지 않는다. 최소 반례의 두 점 분리를 처리할 때 쓴다.
-/

namespace Kuratowski
open SimpleGraph
variable {V : Type*} {G H : SimpleGraph V} {x y : V}

/-- `y`를 `x`로 보내는 꼭짓점 사상. -/
def contractVertex [DecidableEq V] (x y a : V) : V := if a = y then x else a

lemma contractEdge_adj_contractVertex [DecidableEq V] (hxy : x ≠ y) {a b : V}
    (ha : a ≠ x) (hb : b ≠ x) (hab : G.Adj a b) :
    (contractEdge G x y).Adj (contractVertex x y a) (contractVertex x y b) := by
  by_cases hay : a = y
  · subst a
    have hby : b ≠ y := hab.ne.symm
    simp only [contractVertex, ↓reduceIte, hby]
    exact ⟨hb.symm, hxy, hby, Or.inr (Or.inl ⟨rfl, hab⟩)⟩
  by_cases hby : b = y
  · subst b
    have hay' : a ≠ y := hab.ne
    simp only [contractVertex, hay', ↓reduceIte]
    exact ⟨ha, hay', hxy, Or.inr (Or.inr ⟨rfl, hab.symm⟩)⟩
  simp only [contractVertex, hay, hby, ↓reduceIte]
  exact ⟨hab.ne, hay, hby, Or.inl hab⟩

/-- `x`를 피하는 걸음을 `y ↦ x`로 옮긴다. 접히는 변이 없어 길이가 그대로다. -/
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

/-- 부분 그래프도 KF다. -/
theorem KuratowskiFree.mono {G H : SimpleGraph V} (h : KuratowskiFree G) (hle : H ≤ G) :
    KuratowskiFree H := by
  constructor
  · rintro ⟨f, J, hJ, hJG⟩
    exact h.1 ⟨f, J, hJ, hJG.trans hle⟩
  · rintro ⟨f, J, hJ, hJG⟩
    exact h.2 ⟨f, J, hJ, hJG.trans hle⟩

/-- 내부가 부분 그래프의 지지 집합 밖에 있는 경로를 한 변으로 더해도 KF가 유지된다. -/
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

