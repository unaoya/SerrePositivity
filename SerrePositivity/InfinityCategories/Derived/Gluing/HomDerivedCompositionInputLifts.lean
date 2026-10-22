module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCompositionInputSections
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientCompositionLifts

/-! 元の gluing Hom を、元の左右鎖射影を保持して入力付き二合成対応へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomDerivedFirstCompositionInputLift (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
      dgGluingDerivedFirstCompositionInputFiber R C D M X Y :=
  pullback.lift (dgGluingHomDerivedFirstComposition R C D M X Y)
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) (by
      rw [dgGluingHomDerivedFirstComposition_input R C D M X Y,
        dgGluingHomDerivedRightCoefficientInput_raw_factor R C D M X Y])

def dgGluingHomDerivedLastCompositionInputLift (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
      dgGluingDerivedLastCompositionInputFiber R C D M X Y :=
  pullback.lift (dgGluingHomDerivedLastComposition R C D M X Y)
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y))) (by
      rw [dgGluingHomDerivedLastComposition_input R C D M X Y,
        dgGluingHomDerivedLeftCoefficientInput_raw_factor R C D M X Y])

lemma dgGluingHomDerivedFirstCompositionInputLift_input (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedFirstCompositionInputLift R C D M X Y ≫
        dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)) :=
  pullback.lift_snd _ _ _

lemma dgGluingHomDerivedLastCompositionInputLift_input (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedLastCompositionInputLift R C D M X Y ≫
        dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)) :=
  pullback.lift_snd _ _ _

lemma dgGluingHomDerivedFirstCompositionInputLift_composition (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedFirstCompositionInputLift R C D M X Y ≫ pullback.fst _ _ =
      dgGluingHomDerivedFirstComposition R C D M X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingHomDerivedLastCompositionInputLift_composition (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedLastCompositionInputLift R C D M X Y ≫ pullback.fst _ _ =
      dgGluingHomDerivedLastComposition R C D M X Y :=
  pullback.lift_fst _ _ _

end SerrePositivity.InfinityCategories
