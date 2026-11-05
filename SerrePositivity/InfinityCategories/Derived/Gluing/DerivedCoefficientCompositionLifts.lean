module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCoefficientInputs
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstFixedCompositionLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.LastFixedCompositionLift

/-! 左右の元 Hom 入力を持つ二三角形を、同じ実 augmentation の合成対応へ持ち上げる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingUniverseDerivedLeftCoefficientTriangleFamily_variable
    (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingDerivedLeftCoefficientInput R C D M X Y) :=
  (dgGluingUniverseDerivedLeftCoefficientTriangleFamily_two R C D M X Y).trans
    (dgGluingDerivedLeftCoefficientInput_uncurry R C D M X Y).symm

lemma dgGluingUniverseDerivedRightCoefficientTriangleFamily_variable
    (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingDerivedRightCoefficientInput R C D M X Y) :=
  (dgGluingUniverseDerivedRightCoefficientTriangleFamily_zero R C D M X Y).trans
    (dgGluingDerivedRightCoefficientInput_uncurry R C D M X Y).symm

def dgGluingDerivedFirstComposition (X Y : DGGluingObject R C D M) :=
  dgGluingFirstFixedCompositionLift (dgGluingDerivedAugmentationEdge R C D M X)
    ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (DGNerve.Simplex.vertex Y.right)))
    (dgGluingDerivedRightCoefficientInput R C D M X Y)
    (dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y)
    (dgGluingUniverseDerivedRightCoefficientTriangleFamily_fixed R C D M X Y)
    (dgGluingUniverseDerivedRightCoefficientTriangleFamily_variable R C D M X Y)

def dgGluingDerivedLastComposition (X Y : DGGluingObject R C D M) :=
  dgGluingLastFixedCompositionLift
    ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (DGNerve.Simplex.vertex X.left)))
    (dgGluingDerivedAugmentationEdge R C D M Y)
    (dgGluingDerivedLeftCoefficientInput R C D M X Y)
    (dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y)
    (dgGluingUniverseDerivedLeftCoefficientTriangleFamily_variable R C D M X Y)
    (dgGluingUniverseDerivedLeftCoefficientTriangleFamily_fixed R C D M X Y)

lemma dgGluingDerivedFirstComposition_input (X Y : DGGluingObject R C D M) :
    dgGluingDerivedFirstComposition R C D M X Y ≫
        dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
          ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
            (ULift.up (DGNerve.Simplex.vertex Y.right))) =
      dgGluingDerivedRightCoefficientInput R C D M X Y :=
  dgGluingFirstFixedCompositionLift_second _ _ _ _ _ _

lemma dgGluingDerivedLastComposition_input (X Y : DGGluingObject R C D M) :
    dgGluingDerivedLastComposition R C D M X Y ≫
        compositionCorrespondenceFirst
          ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
            (ULift.up (DGNerve.Simplex.vertex X.left)))
          (dgGluingDerivedAugmentationEdge R C D M Y) =
      dgGluingDerivedLeftCoefficientInput R C D M X Y :=
  dgGluingLastFixedCompositionLift_first _ _ _ _ _ _

lemma dgGluingDerivedFirstComposition_triangle (X Y : DGGluingObject R C D M) :
    (Δ[2] ◁ dgGluingDerivedFirstComposition R C D M X Y) ≫
        dgGluingFirstFixedCompositionEvaluation (dgGluingDerivedAugmentationEdge R C D M X)
          ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
            (ULift.up (DGNerve.Simplex.vertex Y.right))) =
      dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y :=
  dgGluingFirstFixedCompositionLift_evaluation _ _ _ _ _ _

lemma dgGluingDerivedLastComposition_triangle (X Y : DGGluingObject R C D M) :
    (Δ[2] ◁ dgGluingDerivedLastComposition R C D M X Y) ≫
        compositionCorrespondenceEvaluation
          ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
            (ULift.up (DGNerve.Simplex.vertex X.left)))
          (dgGluingDerivedAugmentationEdge R C D M Y) =
      dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y :=
  dgGluingLastFixedCompositionLift_evaluation _ _ _ _ _ _

lemma dgGluingDerivedFirstComposition_diagonal (X Y : DGGluingObject R C D M) :
    intervalMappingUncurry (dgGluingDerivedFirstComposition R C D M X Y ≫
      dgGluingFirstFixedCompositionDiagonal (dgGluingDerivedAugmentationEdge R C D M X)
        ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex Y.right)))) =
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
      dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y :=
  dgGluingFirstFixedCompositionLift_diagonal _ _ _ _ _ _

lemma dgGluingDerivedLastComposition_diagonal (X Y : DGGluingObject R C D M) :
    intervalMappingUncurry (dgGluingDerivedLastComposition R C D M X Y ≫
      compositionCorrespondenceDiagonal
        ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex X.left)))
        (dgGluingDerivedAugmentationEdge R C D M Y)) =
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
      dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y :=
  dgGluingLastFixedCompositionLift_diagonal _ _ _ _ _ _

end SerrePositivity.InfinityCategories
