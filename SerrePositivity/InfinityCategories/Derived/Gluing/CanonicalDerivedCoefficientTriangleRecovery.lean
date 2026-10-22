module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CanonicalDerivedCoefficientTriangleFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModuleDerivedCoefficientTriangleFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionTriangleRecovery

/-! 主経路の左右三角形は、native 合成 prism から作った同じ全二単体族そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingModuleDerivedLeftCoefficientTriangleFamily_canonical
    (X Y : DGGluingObject R C D M) :
    dgGluingModuleDerivedLeftCoefficientTriangleFamily R C D M X Y =
      dgGluingCanonicalDerivedLeftCoefficientTriangleFamily R C D M X Y := by
  rw [dgGluingModuleDerivedLeftCoefficientTriangleFamily,
    dgGluingModuleDerivedLeftCoefficientTriangle, dgGluingFunctorTriangleCast_evaluation,
    dgGluingDGCompositionFunctorTriangle_evaluate]
  · rfl
  · rw [dgGluingNativeLeftCoefficientComposition R C D M X Y]

lemma dgGluingModuleDerivedRightCoefficientTriangleFamily_canonical
    (X Y : DGGluingObject R C D M) :
    dgGluingModuleDerivedRightCoefficientTriangleFamily R C D M X Y =
      dgGluingCanonicalDerivedRightCoefficientTriangleFamily R C D M X Y := by
  rw [dgGluingModuleDerivedRightCoefficientTriangleFamily,
    dgGluingModuleDerivedRightCoefficientTriangle, dgGluingFunctorTriangleCast_evaluation,
    dgGluingDGCompositionFunctorTriangle_evaluate]
  · rfl
  · rw [dgGluingNativeRightCoefficientComposition R C D M X Y]

end SerrePositivity.InfinityCategories
