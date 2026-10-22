module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCoefficientIntervalMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCompositionInputDiagonals

/-! 元の左右 Hom 入力による切断の対角は、canonical な実導来係数比較による二作用。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingDerivedLastCompositionInputSection_diagonal (X Y : DGGluingObject R C D M) :
    dgGluingDerivedLastCompositionInputSection R C D M X Y ≫
        dgGluingDerivedLastCompositionInputDiagonal R C D M X Y =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingLeftAction R C D M X Y)) ≫
        dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right ≫
          dgGluingDerivedCoefficientIntervalMap R C D M X.left Y.right := by
  apply intervalMappingUncurry_injective _ _
  rw [dgGluingDerivedLastCompositionInputDiagonal, ← Category.assoc,
    dgGluingDerivedLastCompositionInputSection_composition R C D M X Y,
    dgGluingDerivedLastComposition_diagonal R C D M X Y,
    dgGluingUniverseDerivedLeftCoefficientTriangleFamily_diagonal R C D M X Y]
  simpa only [Category.assoc] using
    (dgGluingDerivedCoefficientIntervalMap_uncurry R C D M X.left Y.right
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingLeftAction R C D M X Y)) ≫
        dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right)).symm

lemma dgGluingDerivedFirstCompositionInputSection_diagonal (X Y : DGGluingObject R C D M) :
    dgGluingDerivedFirstCompositionInputSection R C D M X Y ≫
        dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingRightAction R C D M X Y)) ≫
        dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right ≫
          dgGluingDerivedCoefficientIntervalMap R C D M X.left Y.right := by
  apply intervalMappingUncurry_injective _ _
  rw [dgGluingDerivedFirstCompositionInputDiagonal, ← Category.assoc,
    dgGluingDerivedFirstCompositionInputSection_composition R C D M X Y,
    dgGluingDerivedFirstComposition_diagonal R C D M X Y,
    dgGluingUniverseDerivedRightCoefficientTriangleFamily_diagonal R C D M X Y]
  simpa only [Category.assoc] using
    (dgGluingDerivedCoefficientIntervalMap_uncurry R C D M X.left Y.right
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingRightAction R C D M X Y)) ≫
        dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right)).symm

end SerrePositivity.InfinityCategories
