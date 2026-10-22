module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomTriangleVariableEdges
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowCompositionTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstFixedCompositionExt
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCompositionInputFibers

/-! 元の lax Hom 比較からの二合成対応は、保存済みの元 Hom 入力を厳密に回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingLaxHomArrowCompositionComparison_first_input (X Y : DGGluingObject R C D M) :
    (dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.fst _ _) ≫
        dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
          ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
            (ULift.up (DGNerve.Simplex.vertex Y.right))) =
      dgGluingHomDerivedRightCoefficientInput R C D M X Y := by
  apply intervalMappingUncurry_injective _ _
  rw [dgGluingFirstFixedCompositionSecond_uncurry, uncurry_natural_left]
  change (stdSimplex.δ (0 : Fin 3) ▷ _) ≫
      ((Δ[2] ◁ (dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.fst _ _)) ≫
        dgGluingFirstFixedCompositionEvaluation _ _) = _
  rw [dgGluingLaxHomArrowCompositionComparison_first_triangle R C D M X Y,
    dgGluingLaxHomArrowTriangles_first_variable R C D M X Y]

lemma dgGluingLaxHomArrowCompositionComparison_last_input (X Y : DGGluingObject R C D M) :
    (dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.snd _ _) ≫
        compositionCorrespondenceFirst
          ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
            (ULift.up (DGNerve.Simplex.vertex X.left)))
          (dgGluingDerivedAugmentationEdge R C D M Y) =
      dgGluingHomDerivedLeftCoefficientInput R C D M X Y := by
  apply intervalMappingUncurry_injective _ _
  rw [compositionCorrespondenceFirst_uncurry, uncurry_natural_left]
  change (stdSimplex.δ (2 : Fin 3) ▷ _) ≫
      ((Δ[2] ◁ (dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.snd _ _)) ≫
        compositionCorrespondenceEvaluation _ _) = _
  rw [dgGluingLaxHomArrowCompositionComparison_last_triangle R C D M X Y,
    dgGluingLaxHomArrowTriangles_second_variable R C D M X Y]

end SerrePositivity.InfinityCategories
