module
public import SerrePositivity.KST.Fibration.StraighteningBaseChangeChartComponents

/-! # pullback 側の指定切断比較の端点を、同じ初頂点比較へ揃える -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

/-- 対象変数の前合成は、同じ対象像の二重評価頂点を厳密に回収する。 -/
theorem doubleFunctorEvaluation_post_pre_vertex {A K L Y : SSet.{u}}
    (F : A ⟶ (ihom L).obj Y) (H : K ⟶ L)
    (a : A _⦋0⦌) (x : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation (Y := Y) a x).app (Opposite.op ⦋0⦌)
        (functorVertex (F ≫ (pre H).app Y)) =
      (_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation (Y := Y) a (H.app (Opposite.op ⦋0⦌) x)).app
        (Opposite.op ⦋0⦌) (functorVertex F) := by
  have h := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (functorVertex F))
    (doubleFunctorEvaluation_post_pre H a x)
  change (_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation (Y := Y) a x).app (Opposite.op ⦋0⦌)
    (((ihom A).map ((pre H).app Y)).app (Opposite.op ⦋0⦌) (functorVertex F)) = _ at h
  exact h

/-- 右側の元の分類値は、同じ pullback 対象での初頂点分類値。 -/
theorem straighteningBaseChangeRight_source_vertex
    (X : LeftFibrationObject B) (c : TransportSimplexCategory D) :
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation (Y := SpaceInfinity.{u})
      (ULift.up (nerveVertex c)) (coherentNerveVertex X)).app (Opposite.op ⦋0⦌)
        (functorVertex (((SSet.uliftFunctor.{u + 1, u}).map
          (transportSimplexFirstVertexMap D) ≫ leftStraighteningSectionJointDiagram D) ≫
            (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})) =
      (_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up (nerveVertex c))
        (coherentNerveVertex (leftFibrationBaseChangeObject k X))).app (Opposite.op ⦋0⦌)
          (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
            (transportSimplexFirstVertexMap D) ≫ leftStraighteningSectionJointDiagram D)) := by
  exact (doubleFunctorEvaluation_post_pre_vertex
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D) ≫
      leftStraighteningSectionJointDiagram D)
    (leftFibrationInfinityBaseChange k) (ULift.up (nerveVertex c))
    (coherentNerveVertex X)).trans
      (congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation
        (K := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (TransportSimplexCategory D)))
        (Y := SpaceInfinity.{u}) (ULift.up (nerveVertex c)) z).app (Opposite.op ⦋0⦌)
          (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
            (transportSimplexFirstVertexMap D) ≫ leftStraighteningSectionJointDiagram D)))
        (leftFibrationInfinityBaseChange_vertex k X))

/-- 端点を揃えた右側の指定比較は、同じ pullback 対象の初頂点比較そのもの。 -/
theorem straighteningBaseChangeRightChart_eq_firstVertex
    (X : LeftFibrationObject B) (c : TransportSimplexCategory D) :
    F2.isoNormalizeEndpoints (straighteningBaseChangeRightChart k X c)
      (congrArg HomotopyCategory.mk (straighteningBaseChangeRight_source_vertex k X c)) rfl =
      straighteningFirstVertexSectionChart (leftFibrationBaseChangeObject k X) c :=
  F2.isoNormalizeEndpoints_eq_of_heq _ _ _ _
    (straighteningBaseChangeRightChart_heq_firstVertex k X c)

end SerrePositivity.KST.Fibration
