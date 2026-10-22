module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseAugmentationPrism
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedInfinity

/-! 任意の対象宇宙で、元の加群値二脚を β5 の導来加群 ∞ 圏へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingUniverseModuleDerivedComparison :
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgNerve R (RightModule R C)) ⟶
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C) :=
  (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
    (dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C)))

def dgGluingUniverseDerivedYoneda :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v}).obj (dgNerve R C) ⟶
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C) :=
  dgGluingUniverseYoneda.{u, v, w} R C ≫ dgGluingUniverseModuleDerivedComparison.{u, v, w} R C

def dgGluingUniverseDerivedCoefficient :
    (SSet.uliftFunctor.{max (u + 1) v w, max u w}).obj (dgNerve R D) ⟶
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C) :=
  dgGluingUniverseCoefficient R C D M ≫ dgGluingUniverseModuleDerivedComparison.{u, v, w} R C

def dgGluingUniverseDerivedAugmentationHomotopy :
    SSet.Homotopy
      (dgGluingUniverseLeftNerve R C D M ≫ dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseRightNerve R C D M ≫ dgGluingUniverseDerivedCoefficient R C D M) where
  h := (dgGluingUniverseAugmentationHomotopy R C D M).h ≫
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

end SerrePositivity.InfinityCategories
