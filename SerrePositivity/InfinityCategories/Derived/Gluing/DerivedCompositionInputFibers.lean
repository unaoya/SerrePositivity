module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCoefficientCompositionLifts
public import SerrePositivity.InfinityCategories.Derived.Gluing.TrivialKanSectionEquivalence

/-! 左右の元 Hom 入力を保持する合成対応の実 fiber と、その自明 Kan 射影。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedFirstCompositionInputFiber (X Y : DGGluingObject R C D M) :=
  pullback
    (dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right))))
    (dgGluingDerivedRightCoefficientInput R C D M X Y)

def dgGluingDerivedLastCompositionInputFiber (X Y : DGGluingObject R C D M) :=
  pullback
    (compositionCorrespondenceFirst
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left)))
      (dgGluingDerivedAugmentationEdge R C D M Y))
    (dgGluingDerivedLeftCoefficientInput R C D M X Y)

def dgGluingDerivedFirstCompositionInputProjection (X Y : DGGluingObject R C D M) :=
  pullback.snd
    (dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right))))
    (dgGluingDerivedRightCoefficientInput R C D M X Y)

def dgGluingDerivedLastCompositionInputProjection (X Y : DGGluingObject R C D M) :=
  pullback.snd
    (compositionCorrespondenceFirst
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left)))
      (dgGluingDerivedAugmentationEdge R C D M Y))
    (dgGluingDerivedLeftCoefficientInput R C D M X Y)

lemma dgGluingDerivedFirstCompositionInputProjection_trivialKanFibration
    (X Y : DGGluingObject R C D M) :
    TrivialKanFibration (dgGluingDerivedFirstCompositionInputProjection R C D M X Y) := by
  let : TrivialKanFibration
      (dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
        ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex Y.right)))) :=
    dgGluingFirstFixedCompositionSecond_trivialKanFibration _ _
  exact trivialKanFibration_pullback_snd _ _

lemma dgGluingDerivedLastCompositionInputProjection_trivialKanFibration
    (X Y : DGGluingObject R C D M) :
    TrivialKanFibration (dgGluingDerivedLastCompositionInputProjection R C D M X Y) := by
  let : TrivialKanFibration (compositionCorrespondenceFirst
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left)))
      (dgGluingDerivedAugmentationEdge R C D M Y)) :=
    compositionCorrespondenceFirst_trivialKanFibration _ _
  exact trivialKanFibration_pullback_snd _ _

lemma dgGluingDerivedFirstCompositionInputFiber_kanComplex (X Y : DGGluingObject R C D M) :
    KanComplex (dgGluingDerivedFirstCompositionInputFiber R C D M X Y) := by
  let := dgGluingDerivedFirstCompositionInputProjection_trivialKanFibration R C D M X Y
  exact dgGluingTrivialKanProjection_kanComplex
    (dgGluingDerivedFirstCompositionInputProjection R C D M X Y)

lemma dgGluingDerivedLastCompositionInputFiber_kanComplex (X Y : DGGluingObject R C D M) :
    KanComplex (dgGluingDerivedLastCompositionInputFiber R C D M X Y) := by
  let := dgGluingDerivedLastCompositionInputProjection_trivialKanFibration R C D M X Y
  exact dgGluingTrivialKanProjection_kanComplex
    (dgGluingDerivedLastCompositionInputProjection R C D M X Y)

end SerrePositivity.InfinityCategories
