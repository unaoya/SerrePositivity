module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseAugmentationPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedInfinity

/-! 任意の対象宇宙で、元の加群値二脚を β5 の導来加群 ∞ 圏へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)

def dgGluingUniverseModuleDerivedComparison :
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R C)) ⟶
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R C) :=
  (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C)))

def dgGluingUniverseDerivedYoneda :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) ⟶
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R C) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseYoneda.{u, v, w} R C ≫ dgGluingUniverseModuleDerivedComparison.{u, v, w} R C

def dgGluingUniverseDerivedCoefficient :
    (SSet.uliftFunctor.{max (u + 1) v w, max u w}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) ⟶
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R C) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseCoefficient R C D M ≫ dgGluingUniverseModuleDerivedComparison.{u, v, w} R C

def dgGluingUniverseDerivedAugmentationHomotopy :
    SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseLeftNerve R C D M ≫ dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve R C D M ≫ dgGluingUniverseDerivedCoefficient R C D M) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseAugmentationHomotopy R C D M).h ≫
    dgGluingUniverseModuleDerivedComparison.{u, v, w} R C
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
