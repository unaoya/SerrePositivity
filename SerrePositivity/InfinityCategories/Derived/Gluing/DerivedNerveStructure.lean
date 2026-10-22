module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NerveStructure
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedInfinity

/-! β5 の実半自由出力分解で、同じ二脚と augmentation を導来加群 ∞ 圏へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R]
  (C D : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C] [DGCategory R D]
  (M : Bimodule R C D)

def dgGluingModuleDerivedComparison :
    dgNerve R (RightModule R C) ⟶ dgModuleDerivedInfinityCategory R C :=
  dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C))

def dgGluingDerivedYoneda : dgNerve R C ⟶ dgModuleDerivedInfinityCategory R C :=
  dgNerve.map (dgYoneda R C) ≫ dgGluingModuleDerivedComparison R C

def dgGluingDerivedCoefficient : dgNerve R D ⟶ dgModuleDerivedInfinityCategory R C :=
  dgNerve.map M.toFunctor ≫ dgGluingModuleDerivedComparison R C

def dgGluingDerivedAugmentationHomotopy :
    SSet.Homotopy
      (dgGluingLeftNerve R C D M ≫ dgGluingDerivedYoneda R C)
      (dgGluingRightNerve R C D M ≫ dgGluingDerivedCoefficient R C D M) where
  h := (dgGluingAugmentationNerveHomotopy R C D M).h ≫ dgGluingModuleDerivedComparison R C
  h₀ := by
    rw [← Category.assoc, SSet.Homotopy.h₀, Category.assoc]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.Homotopy.h₁, Category.assoc]
    rfl
  rel := by
    ext n s
    exact False.elim s.1.2

end SerrePositivity.InfinityCategories
