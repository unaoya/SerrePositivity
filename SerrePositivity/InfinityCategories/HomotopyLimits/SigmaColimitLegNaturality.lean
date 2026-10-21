module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafColimitLegNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaPresheafLegBottom

/-!
概要：元の有限評価脚の Kan 辺と実際の頂点脚の可換式を同じ coslice 代表で保持する。
方針：実際の余錐脚の底変換を、元の同じ評価脚変換へ厳密に照合する。
規約：元の各代表辺と全一単体を保持する。有限性は不要。
使われ方：実際の全錐像と標準全錐への端点表示の輸送。
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
  {J : Type u} {p : nerve (Discrete J) ⟶ C.op}
  (c : JoinCone p) (j : J)
local notation "x₀" => JoinCone.vertex (JoinCone.ulift c)
local notation "x₁" => NatTrans.app (CategoryTheory.Functor.map SSet.uliftFunctor p)
  (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk j)))
local notation "A" => sigmaPresheafVertexEvaluation r x₀
local notation "G" => sigmaPresheafFiniteEvaluationFamily r (p := p)
local notation "q₀" => F1B.kanPostcomposeCocone (evaluateFunctorAt x₀) q
local notation "q₁" => F1B.kanPostcomposeCocone (evaluateFunctorAt x₁) q

/-- 同じ元の代表の間で、指定評価脚の Kan 辺と元の実際の頂点脚は可換。 -/
lemma sigmaColimitLeg_representative_naturality :
    homMk (presheafEvaluationComparisonApexEdge
      (r ≫ sigmaPresheafInfinityInclusion C) q hq x₀) ≫
      homMk (totalKanNativeEdge A (G j) (coherentTransformationTotalKanMap A (G j)
        (sigmaPresheafConeLegTransformation r c j))).toTruncated =
    homMk (coconeWholeEdgeApex q₀ q₁ (presheafCoconeImageLeg q c
      (ULift.up (nerveVertex (Discrete.mk j)))).toTruncated).toTruncated ≫
      homMk (presheafEvaluationComparisonApexEdge
        (r ≫ sigmaPresheafInfinityInclusion C) q hq x₁) ≫
      eqToHom (congrArg HomotopyCategory.mk (F2.coherentDiagramTotalCocone_vertex (G j))) := by
  have H := presheafColimitLeg_representative_naturality q hq c
    (ULift.up (nerveVertex (Discrete.mk j)))
  have ht := sigmaPresheafCoconeBottomLeg_vertex r q c j
  change intervalMappingVertexOfEdge (coconeWholeEdgeBottom q₀ q₁
    (presheafCoconeImageLeg q c (ULift.up (nerveVertex (Discrete.mk j)))).toTruncated) = _ at ht
  rw [ht] at H
  exact H

end SerrePositivity.InfinityCategories.HomotopyLimits
