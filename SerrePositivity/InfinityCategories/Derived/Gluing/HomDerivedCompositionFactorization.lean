module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCompositionInputLifts

/-! 全 gluing Hom 上の二合成三角形は、元の左右 Hom 射影を通して厳密に因子分解する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomDerivedFirstComposition_factor (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedFirstComposition R C D M X Y =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)) ≫
        dgGluingDerivedFirstComposition R C D M X Y := by
  apply pullback.hom_ext
  · rw [dgGluingHomDerivedFirstComposition, dgGluingFirstFixedCompositionLift_triangle,
      Category.assoc, dgGluingDerivedFirstComposition,
      dgGluingFirstFixedCompositionLift_triangle]
    apply uncurry_injective
    rw [uncurry_curry, uncurry_natural_left, uncurry_curry]
    rfl
  · change dgGluingHomDerivedFirstComposition R C D M X Y ≫
      dgGluingFirstFixedCompositionSecond _ _ = _
    rw [dgGluingHomDerivedFirstComposition_input R C D M X Y]
    change _ = _ ≫ (dgGluingDerivedFirstComposition R C D M X Y ≫
      dgGluingFirstFixedCompositionSecond _ _)
    rw [dgGluingDerivedFirstComposition_input R C D M X Y,
      dgGluingHomDerivedRightCoefficientInput_raw_factor R C D M X Y]

lemma dgGluingHomDerivedLastComposition_factor (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedLastComposition R C D M X Y =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)) ≫
        dgGluingDerivedLastComposition R C D M X Y := by
  apply pullback.hom_ext
  · rw [dgGluingHomDerivedLastComposition, dgGluingLastFixedCompositionLift_triangle,
      Category.assoc, dgGluingDerivedLastComposition,
      dgGluingLastFixedCompositionLift_triangle]
    apply uncurry_injective
    rw [uncurry_curry, uncurry_natural_left, uncurry_curry]
    rfl
  · change dgGluingHomDerivedLastComposition R C D M X Y ≫
      compositionCorrespondenceFirst _ _ = _
    rw [dgGluingHomDerivedLastComposition_input R C D M X Y]
    change _ = _ ≫ (dgGluingDerivedLastComposition R C D M X Y ≫
      compositionCorrespondenceFirst _ _)
    rw [dgGluingDerivedLastComposition_input R C D M X Y,
      dgGluingHomDerivedLeftCoefficientInput_raw_factor R C D M X Y]

end SerrePositivity.InfinityCategories
