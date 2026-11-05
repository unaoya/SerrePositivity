module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCompositionInputLifts
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCompositionDiagonalPath

/-! 入力付き合成対応の対角は、元の同じ二合成対角を保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedFirstCompositionInputDiagonal (X Y : DGGluingObject R C D M) :=
  pullback.fst
      (dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
        ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex Y.right))))
      (dgGluingDerivedRightCoefficientInput R C D M X Y) ≫
    dgGluingFirstFixedCompositionDiagonal (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right)))

def dgGluingDerivedLastCompositionInputDiagonal (X Y : DGGluingObject R C D M) :=
  pullback.fst
      (compositionCorrespondenceFirst
        ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex X.left)))
        (dgGluingDerivedAugmentationEdge R C D M Y))
      (dgGluingDerivedLeftCoefficientInput R C D M X Y) ≫
    compositionCorrespondenceDiagonal
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left)))
      (dgGluingDerivedAugmentationEdge R C D M Y)

lemma dgGluingHomDerivedFirstCompositionInputLift_diagonal (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedFirstCompositionInputLift R C D M X Y ≫
        dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y =
      dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y := by
  rw [dgGluingDerivedFirstCompositionInputDiagonal, ← Category.assoc,
    dgGluingHomDerivedFirstCompositionInputLift_composition R C D M X Y]
  rfl

lemma dgGluingHomDerivedLastCompositionInputLift_diagonal (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedLastCompositionInputLift R C D M X Y ≫
        dgGluingDerivedLastCompositionInputDiagonal R C D M X Y =
      dgGluingHomDerivedLastCompositionDiagonal R C D M X Y := by
  rw [dgGluingDerivedLastCompositionInputDiagonal, ← Category.assoc,
    dgGluingHomDerivedLastCompositionInputLift_composition R C D M X Y]
  rfl

end SerrePositivity.InfinityCategories
