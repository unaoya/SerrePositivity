module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientVariableEdges
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstFixedCompositionLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.LastFixedCompositionLift

/-! 元の二三角形を、主比較の同じ augmentation を持つ二合成対応へ持ち上げる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomDerivedFirstComposition (X Y : DGGluingObject R C D M) :=
  dgGluingFirstFixedCompositionLift (dgGluingDerivedAugmentationEdge R C D M X)
    ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (DGNerve.Simplex.vertex Y.right)))
    (dgGluingHomDerivedRightCoefficientInput R C D M X Y)
    (dgGluingHomDerivedRightCoefficientTriangle R C D M X Y)
    (dgGluingHomDerivedRightCoefficientTriangle_fixed R C D M X Y)
    (dgGluingHomDerivedRightCoefficientTriangle_variable R C D M X Y)

def dgGluingHomDerivedLastComposition (X Y : DGGluingObject R C D M) :=
  dgGluingLastFixedCompositionLift
    ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (DGNerve.Simplex.vertex X.left)))
    (dgGluingDerivedAugmentationEdge R C D M Y)
    (dgGluingHomDerivedLeftCoefficientInput R C D M X Y)
    (dgGluingHomDerivedLeftCoefficientTriangle R C D M X Y)
    (dgGluingHomDerivedLeftCoefficientTriangle_variable R C D M X Y)
    (dgGluingHomDerivedLeftCoefficientTriangle_fixed R C D M X Y)

lemma dgGluingHomDerivedFirstComposition_input (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedFirstComposition R C D M X Y ≫
        dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
          ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
            (ULift.up (DGNerve.Simplex.vertex Y.right))) =
      dgGluingHomDerivedRightCoefficientInput R C D M X Y :=
  dgGluingFirstFixedCompositionLift_second _ _ _ _ _ _

lemma dgGluingHomDerivedLastComposition_input (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedLastComposition R C D M X Y ≫
        compositionCorrespondenceFirst
          ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
            (ULift.up (DGNerve.Simplex.vertex X.left)))
          (dgGluingDerivedAugmentationEdge R C D M Y) =
      dgGluingHomDerivedLeftCoefficientInput R C D M X Y :=
  dgGluingLastFixedCompositionLift_first _ _ _ _ _ _

lemma dgGluingHomDerivedFirstComposition_triangle (X Y : DGGluingObject R C D M) :
    (Δ[2] ◁ dgGluingHomDerivedFirstComposition R C D M X Y) ≫
        dgGluingFirstFixedCompositionEvaluation (dgGluingDerivedAugmentationEdge R C D M X)
          ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
            (ULift.up (DGNerve.Simplex.vertex Y.right))) =
      dgGluingHomDerivedRightCoefficientTriangle R C D M X Y :=
  dgGluingFirstFixedCompositionLift_evaluation _ _ _ _ _ _

lemma dgGluingHomDerivedLastComposition_triangle (X Y : DGGluingObject R C D M) :
    (Δ[2] ◁ dgGluingHomDerivedLastComposition R C D M X Y) ≫
        compositionCorrespondenceEvaluation
          ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
            (ULift.up (DGNerve.Simplex.vertex X.left)))
          (dgGluingDerivedAugmentationEdge R C D M Y) =
      dgGluingHomDerivedLeftCoefficientTriangle R C D M X Y :=
  dgGluingLastFixedCompositionLift_evaluation _ _ _ _ _ _

lemma dgGluingHomDerivedFirstComposition_diagonal (X Y : DGGluingObject R C D M) :
    intervalMappingUncurry (dgGluingHomDerivedFirstComposition R C D M X Y ≫
      dgGluingFirstFixedCompositionDiagonal (dgGluingDerivedAugmentationEdge R C D M X)
        ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex Y.right)))) =
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫ dgGluingHomDerivedRightCoefficientTriangle R C D M X Y :=
  dgGluingFirstFixedCompositionLift_diagonal _ _ _ _ _ _

lemma dgGluingHomDerivedLastComposition_diagonal (X Y : DGGluingObject R C D M) :
    intervalMappingUncurry (dgGluingHomDerivedLastComposition R C D M X Y ≫
      compositionCorrespondenceDiagonal
        ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex X.left)))
        (dgGluingDerivedAugmentationEdge R C D M Y)) =
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫ dgGluingHomDerivedLeftCoefficientTriangle R C D M X Y :=
  dgGluingLastFixedCompositionLift_diagonal _ _ _ _ _ _

end SerrePositivity.InfinityCategories
