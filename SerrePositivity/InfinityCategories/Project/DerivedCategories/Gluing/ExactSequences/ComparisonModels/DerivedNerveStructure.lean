module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.NerveStructure
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedInfinity

/-! β5 の実半自由出力分解で、同じ二脚と augmentation を導来加群 ∞ 圏へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R]
  (C D : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
  (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)

def dgGluingModuleDerivedComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R C) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R C :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C))

def dgGluingDerivedYoneda : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgYoneda R C) ≫ dgGluingModuleDerivedComparison R C

def dgGluingDerivedCoefficient : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map M.toFunctor ≫ dgGluingModuleDerivedComparison R C

def dgGluingDerivedAugmentationHomotopy :
    SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftNerve R C D M ≫ dgGluingDerivedYoneda R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightNerve R C D M ≫ dgGluingDerivedCoefficient R C D M) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentationNerveHomotopy R C D M).h ≫ dgGluingModuleDerivedComparison R C
  h₀ := by
    rw [← Category.assoc, SSet.Homotopy.h₀, Category.assoc]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.Homotopy.h₁, Category.assoc]
    rfl
  rel := by
    ext n s
    exact False.elim s.1.2

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
