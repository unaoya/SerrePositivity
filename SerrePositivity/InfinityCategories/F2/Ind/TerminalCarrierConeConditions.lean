module

public import SerrePositivity.InfinityCategories.F2.Ind.CarrierConeVertices
public import SerrePositivity.InfinityCategories.F2.Ind.TerminalCarrierBound

/-!
概要：元の実現図式と同じ指定頂点への余錐は、全鎖の実現条件を満たす。
方針：元の単体では元の条件を使い、新しい単体では最後の添字と共通部分複体を使う。
規約：値・添字・指定頂点の元の等式を全て保持する。
使われ方：有限 coslice 余錐の二成分を実現空間内へ貼り合わせる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Preorder I] {X K : SSet.{u}}
  (A : I → X.Subcomplex) (z : I → X _⦋0⦌)
  (a : K ⟶ (terminalCarrier A z).toSSet)
  (F : join K (Δ[0] : SSet.{u}) ⟶ X) (q : join K (Δ[0] : SSet.{u}) ⟶ nerve I) (i : I)
  (hF : joinInl K Δ[0] ≫ F = a ≫ terminalCarrierValue A z)
  (hq : joinInl K Δ[0] ≫ q = a ≫ terminalCarrierProjection A z)
  (hbound : Subcomplex.range F ≤ A i)
  (hFapex : F.app _ (coneApex K) = z i) (hqapex : q.app _ (coneApex K) = nerveVertex i)
include hF hq hbound hFapex hqapex

/-- 元の余錐の二成分は、各単体の所属と元の頂点の条件を同時に満たす。 -/
lemma terminalCarrierCone_conditions :
    (∀ (n : SimplexCategoryᵒᵖ) (s : (join K (Δ[0] : SSet.{u})).obj n),
      F.app n s ∈ (A ((q.app n s).obj (Fin.last n.unop.len))).obj n) ∧
    ∀ v : (join K (Δ[0] : SSet.{u})) _⦋0⦌, F.app _ v = z ((q.app _ v).obj 0) := by
  constructor
  · rintro ⟨⟨n⟩⟩ s
    rcases coneSimplex_inl_or_last_apex s with ⟨x, rfl⟩ | hs
    · have hf := congrArg (fun f : K ⟶ X => f.app _ x) hF
      have hqq := congrArg (fun f : K ⟶ nerve I => f.app _ x) hq
      change F.app _ ((joinInl K Δ[0]).app _ x) = (a.app _ x).val.1 at hf
      change q.app _ ((joinInl K Δ[0]).app _ x) = (a.app _ x).val.2 at hqq
      rw [hf, hqq]
      exact terminalCarrierCondition_mem_last (a.app _ x).property
    · rw [coneMap_last_index q i hqapex s hs]
      exact hbound _ ⟨s, rfl⟩
  · intro v
    rcases coneSimplex_inl_or_last_apex v with ⟨x, rfl⟩ | hs
    · have hf := congrArg (fun f : K ⟶ X => f.app _ x) hF
      have hqq := congrArg (fun f : K ⟶ nerve I => f.app _ x) hq
      change F.app _ ((joinInl K Δ[0]).app _ x) = (a.app _ x).val.1 at hf
      change q.app _ ((joinInl K Δ[0]).app _ x) = (a.app _ x).val.2 at hqq
      rw [hf, hqq]
      exact terminalCarrier_vertex_value (a.app _ x)
    · have hv : v = coneApex K := by
        apply (coneVertex_eq_apex_iff v).mpr
        have hh := (coneSimplexVertex_eq_apex_iff v (Fin.last 0)).mp hs
        change v.1.val ≤ 0 at hh
        omega
      rw [hv, hFapex, hqapex]
      rfl

end SerrePositivity.InfinityCategories.F2.Ind
