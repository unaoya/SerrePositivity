module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaColimitComparisonEdges
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaColimitLegNaturality

/-!
概要：実際の有限錐像と標準有限積全錐の同じ比較辺に、元の全脚の可換式を移す。
方針：同じ coslice 代表の頂点類と標準 Kan 脚の式を、四端点の等式で輸送する。
規約：元の実際の脚・標準脚・共有頂点代表・成分比較の全一単体を保持する。
使われ方：全錐の関手同型と非空有限積保存の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
  (q : JoinCocone (r ≫ sigmaPresheafInfinityInclusion C))
  (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
    IsColimitCone (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q))
  {J : Type u} [Finite J] [Nonempty J] {p : nerve (Discrete J) ⟶ C.op}
  (c : JoinCone p) (j : J)
local notation "x₀" => JoinCone.vertex (JoinCone.ulift c)
local notation "x₁" => NatTrans.app (CategoryTheory.Functor.map SSet.uliftFunctor p)
  (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk j)))
local notation "A" => sigmaPresheafVertexEvaluation r x₀
local notation "G" => sigmaPresheafFiniteEvaluationFamily r (p := p)
local notation "q₀" => F1B.kanPostcomposeCocone (evaluateFunctorAt x₀) q
local notation "q₁" => F1B.kanPostcomposeCocone (evaluateFunctorAt x₁) q

/-- 同じ元の頂点比較・成分比較の間で、実際の全錐脚と標準全錐脚は可換。 -/
lemma sigmaColimitComparisonLeg_commutes :
    homMk (sigmaColimitApexComparisonEdge r q hq c).toTruncated ≫
      homMk (F2.nativeConeLeg (sigmaPresheafColimitFiniteCone r c)
        (ULift.up (nerveVertex (Discrete.mk j)))) =
    homMk (F2.nativeConeLeg (mapJoinCone (presheafCoconeVertexFunctor q) (JoinCone.ulift c))
      (ULift.up (nerveVertex (Discrete.mk j)))) ≫
      homMk (sigmaColimitComponentComparisonEdge r q hq (p := p) j).toTruncated := by
  let ambient := r ≫ sigmaPresheafInfinityInclusion C
  let P₀ := presheafEvaluationComparisonApexEdge ambient q hq x₀
  let P₁ := presheafEvaluationComparisonApexEdge ambient q hq x₁
  let b : SpaceInfinity.{u}.Edge (JoinCocone.vertex q₁) (F2.coherentDiagramTotalVertex (G j)) :=
    (SSet.Edge.ofTruncated P₁).ofEq rfl (F2.coherentDiagramTotalCocone_vertex (G j))
  have H := sigmaColimitLeg_representative_naturality r q hq c j
  have hb : homMk P₁ ≫ eqToHom (congrArg HomotopyCategory.mk
      (F2.coherentDiagramTotalCocone_vertex (G j))) = homMk b.toTruncated :=
    homMk_comp_eqToHom_of_edge_eq P₁ b.toTruncated
      (F2.coherentDiagramTotalCocone_vertex (G j)) rfl
  rw [hb] at H
  exact F2.homMk_square_transport P₀
    (totalKanNativeEdge A (G j) (coherentTransformationTotalKanMap A (G j)
      (sigmaPresheafConeLegTransformation r c j))).toTruncated
    (coconeWholeEdgeApex q₀ q₁ (presheafCoconeImageLeg q c
      (ULift.up (nerveVertex (Discrete.mk j)))).toTruncated).toTruncated b.toTruncated
    (sigmaColimitApexComparisonEdge r q hq c).toTruncated
    (F2.nativeConeLeg (sigmaPresheafColimitFiniteCone r c)
      (ULift.up (nerveVertex (Discrete.mk j))))
    (F2.nativeConeLeg (mapJoinCone (presheafCoconeVertexFunctor q) (JoinCone.ulift c))
      (ULift.up (nerveVertex (Discrete.mk j))))
    (sigmaColimitComponentComparisonEdge r q hq (p := p) j).toTruncated H
    ((presheafCoconeEvaluation_vertex q x₀).trans
      (mapJoinCone_vertex (presheafCoconeVertexFunctor q) (JoinCone.ulift c)).symm)
    ((F2.coherentDiagramTotalCocone_vertex A).trans
      ((spaceInfinityVertex_eq_coherent (F2.coherentDiagramTotalKanObject A)).trans
        (sigmaPresheafColimitFiniteCone_vertex r c).symm))
    (presheafCoconeEvaluation_vertex q x₁)
    (kanDiagramCoherentNerve_vertex (Discrete.functor
      (fun j => F2.coherentDiagramTotalKanObject (G j))) (Discrete.mk j)).symm
    rfl (sigmaPresheafColimitFiniteCone_originalLeg_edge r c j).symm
    (presheafCoconeImageLeg_apex q c (ULift.up (nerveVertex (Discrete.mk j)))) rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
