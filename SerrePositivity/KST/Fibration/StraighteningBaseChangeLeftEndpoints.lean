module
public import SerrePositivity.InfinityCategories.Stable.Straightening.StraighteningBaseChangeLeftEndpoints
public import SerrePositivity.KST.Fibration.DoubleEvaluationPrecompositionVertices
public import SerrePositivity.KST.Fibration.StraighteningBaseChangeChartComponents

/-! # 像の単体での指定切断比較を、元の左底変換比較の端点へ揃える -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

/-- 左側の元の分類値は、同じ像の単体での初頂点分類値。 -/
theorem straighteningBaseChangeLeft_source_vertex
    (X : LeftFibrationObject B) (c : TransportSimplexCategory D) :
    (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
      (ULift.up (nerveVertex c)) (coherentNerveVertex X)).app (Opposite.op ⦋0⦌)
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
          (transportSimplexFirstVertexMap D) ≫
            ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningSectionJointDiagram B))) =
      (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up (nerveVertex ((transportSimplexFunctor k).obj c)))
        (coherentNerveVertex X)).app (Opposite.op ⦋0⦌)
          (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
            (transportSimplexFirstVertexMap B) ≫ leftStraighteningSectionJointDiagram B)) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let t := U.map (nerveMap (transportSimplexFunctor k))
  let F := U.map (transportSimplexFirstVertexMap B) ≫ leftStraighteningSectionJointDiagram B
  have hleft : U.map (transportSimplexFirstVertexMap D) ≫
      (U.map k ≫ leftStraighteningSectionJointDiagram B) = t ≫ F := by
    rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k, Category.assoc]
  exact (congrArg (fun f : U.obj (nerve (TransportSimplexCategory D)) ⟶
      (ihom (LeftFibrationInfinity B)).obj SpaceInfinity.{u} =>
      (doubleFunctorEvaluation
        (K := U.obj (nerve (TransportSimplexCategory D)))
        (A := LeftFibrationInfinity B) (Y := SpaceInfinity.{u})
        (ULift.up (nerveVertex c)) (coherentNerveVertex X)).app (Opposite.op ⦋0⦌)
      (functorVertex f)) hleft).trans
    (doubleFunctorEvaluation_precomp_vertex_of_eq F t (ULift.up (nerveVertex c))
      (coherentNerveVertex X)
      (ULift.up (nerveVertex ((transportSimplexFunctor k).obj c))) rfl)

/-- 両端点を揃えた左の指定比較は、同じ像の単体での初頂点比較そのもの。 -/
theorem straighteningBaseChangeLeftChart_eq_firstVertex
    (X : LeftFibrationObject B) (c : TransportSimplexCategory D) :
    F2.isoNormalizeEndpoints (straighteningBaseChangeLeftChart k X c)
      (congrArg HomotopyCategory.mk (straighteningBaseChangeLeft_source_vertex k X c))
      (congrArg HomotopyCategory.mk (congrArg spaceInfinityVertex
        (straighteningBaseChangeLeft_section_eq k X c))) =
      straighteningFirstVertexSectionChart X ((transportSimplexFunctor k).obj c) :=
  F2.isoNormalizeEndpoints_eq_of_heq _ _ _ _
    (straighteningBaseChangeLeftChart_heq_firstVertex k X c)

end SerrePositivity.KST.Fibration
