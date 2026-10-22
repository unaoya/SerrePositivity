module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowTriangles

/-! 合成対角引き戻しへ移した元の比較は、同じ実二三角形を全パラメーターで回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingLaxHomArrowCompositionComparison_first_triangle
    (X Y : DGGluingObject R C D M) :
    (Δ[2] ◁ (dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.fst _ _)) ≫
      dgGluingFirstFixedCompositionEvaluation (dgGluingDerivedAugmentationEdge R C D M X)
        ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (Simplex.vertex Y.right))) =
      (dgGluingLaxHomArrowTriangles R C D M X Y).first := by
  rw [dgGluingLaxHomArrowCompositionComparison_first, dgGluingArrowHomFirstComposition,
    dgGluingFirstFixedCompositionLift_evaluation]
  rfl

lemma dgGluingLaxHomArrowCompositionComparison_last_triangle
    (X Y : DGGluingObject R C D M) :
    (Δ[2] ◁ (dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.snd _ _)) ≫
      compositionCorrespondenceEvaluation
        ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (Simplex.vertex X.left)))
        (dgGluingDerivedAugmentationEdge R C D M Y) =
      (dgGluingLaxHomArrowTriangles R C D M X Y).second := by
  rw [dgGluingLaxHomArrowCompositionComparison_last, dgGluingArrowHomLastComposition,
    dgGluingLastFixedCompositionLift_evaluation]
  rfl

end SerrePositivity.InfinityCategories
