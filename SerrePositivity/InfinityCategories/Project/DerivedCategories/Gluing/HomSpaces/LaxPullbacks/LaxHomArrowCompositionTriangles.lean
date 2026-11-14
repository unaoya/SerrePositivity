module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.LaxPullbacks.LaxHomArrowComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.LaxPullbacks.LaxHomArrowTriangles

/-! 合成対角引き戻しへ移した元の比較は、同じ実二三角形を全パラメーターで回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)

lemma dgGluingLaxHomArrowCompositionComparison_first_triangle
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (Δ[2] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.fst _ _)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M X)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.right))) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowTriangles R C D M X Y).first := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowCompositionComparison_first, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomFirstComposition,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionLift_evaluation]
  rfl

lemma dgGluingLaxHomArrowCompositionComparison_last_triangle
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (Δ[2] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.snd _ _)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.left)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M Y) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowTriangles R C D M X Y).second := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowCompositionComparison_last, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomLastComposition,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastFixedCompositionLift_evaluation]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
