module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCompositionFactorization

/-! 入力付き合成対応への実比較は、元の左右鎖射影と保存済みの具体的切断の合成。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomDerivedFirstCompositionInputLift_factor (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedFirstCompositionInputLift R C D M X Y =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)) ≫
        dgGluingDerivedFirstCompositionInputSection R C D M X Y := by
  apply pullback.hom_ext
  · rw [dgGluingHomDerivedFirstCompositionInputLift_composition R C D M X Y,
      Category.assoc, dgGluingDerivedFirstCompositionInputSection_composition R C D M X Y,
      dgGluingHomDerivedFirstComposition_factor R C D M X Y]
  · change _ ≫ dgGluingDerivedFirstCompositionInputProjection R C D M X Y = _
    rw [dgGluingHomDerivedFirstCompositionInputLift_input R C D M X Y]
    change _ = _ ≫ (dgGluingDerivedFirstCompositionInputSection R C D M X Y ≫
      dgGluingDerivedFirstCompositionInputProjection R C D M X Y)
    rw [dgGluingDerivedFirstCompositionInputSection_input R C D M X Y, Category.comp_id]

lemma dgGluingHomDerivedLastCompositionInputLift_factor (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedLastCompositionInputLift R C D M X Y =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)) ≫
        dgGluingDerivedLastCompositionInputSection R C D M X Y := by
  apply pullback.hom_ext
  · rw [dgGluingHomDerivedLastCompositionInputLift_composition R C D M X Y,
      Category.assoc, dgGluingDerivedLastCompositionInputSection_composition R C D M X Y,
      dgGluingHomDerivedLastComposition_factor R C D M X Y]
  · change _ ≫ dgGluingDerivedLastCompositionInputProjection R C D M X Y = _
    rw [dgGluingHomDerivedLastCompositionInputLift_input R C D M X Y]
    change _ = _ ≫ (dgGluingDerivedLastCompositionInputSection R C D M X Y ≫
      dgGluingDerivedLastCompositionInputProjection R C D M X Y)
    rw [dgGluingDerivedLastCompositionInputSection_input R C D M X Y, Category.comp_id]

end SerrePositivity.InfinityCategories
