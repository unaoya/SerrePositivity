module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CanonicalDerivedCoefficientTriangleFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModuleDerivedCoefficientTriangleFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGCompositionTriangleRecovery

/-! 主経路の左右三角形は、native 合成 prism から作った同じ全二単体族そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingModuleDerivedLeftCoefficientTriangleFamily_canonical
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedLeftCoefficientTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalDerivedLeftCoefficientTriangleFamily R C D M X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedLeftCoefficientTriangleFamily,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedLeftCoefficientTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorTriangleCast_evaluation,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionFunctorTriangle_evaluate]
  · rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeLeftCoefficientComposition R C D M X Y]

lemma dgGluingModuleDerivedRightCoefficientTriangleFamily_canonical
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedRightCoefficientTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCanonicalDerivedRightCoefficientTriangleFamily R C D M X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedRightCoefficientTriangleFamily,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedRightCoefficientTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorTriangleCast_evaluation,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionFunctorTriangle_evaluate]
  · rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeRightCoefficientComposition R C D M X Y]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
