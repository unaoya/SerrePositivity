module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomCompositionInputs

/-! 元の lax Hom 比較を、元の左右 Hom 鎖射影を保持して入力付き二合成対応へ持ち上げる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingLaxHomFirstCompositionInputLift (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
      dgGluingDerivedFirstCompositionInputFiber R C D M X Y :=
  pullback.lift (dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.fst _ _)
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)))
    ((dgGluingLaxHomArrowCompositionComparison_first_input R C D M X Y).trans
      (dgGluingHomDerivedRightCoefficientInput_raw_factor R C D M X Y))

def dgGluingLaxHomLastCompositionInputLift (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
      dgGluingDerivedLastCompositionInputFiber R C D M X Y :=
  pullback.lift (dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.snd _ _)
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)))
    ((dgGluingLaxHomArrowCompositionComparison_last_input R C D M X Y).trans
      (dgGluingHomDerivedLeftCoefficientInput_raw_factor R C D M X Y))

lemma dgGluingLaxHomFirstCompositionInputLift_composition (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomFirstCompositionInputLift R C D M X Y ≫ pullback.fst _ _ =
      dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

lemma dgGluingLaxHomLastCompositionInputLift_composition (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomLastCompositionInputLift R C D M X Y ≫ pullback.fst _ _ =
      dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.snd _ _ :=
  pullback.lift_fst _ _ _

lemma dgGluingLaxHomFirstCompositionInputLift_input (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomFirstCompositionInputLift R C D M X Y ≫
        dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)) :=
  pullback.lift_snd _ _ _

lemma dgGluingLaxHomLastCompositionInputLift_input (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomLastCompositionInputLift R C D M X Y ≫
        dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)) :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories
