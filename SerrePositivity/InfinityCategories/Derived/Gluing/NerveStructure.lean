module
public import SerrePositivity.InfinityCategories.Derived.Gluing.Projections
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugUnlifted

/-! 共通対象宇宙における dg nerve の実二射影と、元の augmentation の全単体構造変換。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C] [DGCategory R D]
  (M : Bimodule R C D)

def dgGluingLeftNerve : dgNerve R (DGGluingObject R C D M) ⟶ dgNerve R C :=
  dgNerve.map (dgGluingLeft R C D M)

def dgGluingRightNerve : dgNerve R (DGGluingObject R C D M) ⟶ dgNerve R D :=
  dgNerve.map (dgGluingRight R C D M)

def dgGluingAugmentationNerveHomotopy :
    SSet.Homotopy
      (dgGluingLeftNerve R C D M ≫ dgNerve.map (dgYoneda R C))
      (dgGluingRightNerve R C D M ≫ dgNerve.map M.toFunctor) where
  h := (dgNerve.map (dgGluingToComma R C D M) ▷ (Δ[1] : SSet)) ≫
    (dgCommaAugmentationUnliftedHomotopy R D (RightModule R C) M.toFunctor).h
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc,
      SSet.Homotopy.h₀, ← dgNerve.map_comp]
    change dgNerve.map (dgGluingLeftModule R C D M) = _
    rw [dgGluingLeftNerve, ← dgNerve.map_comp, dgGluingLeft_comp_yoneda]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc,
      SSet.Homotopy.h₁, ← dgNerve.map_comp]
    rw [dgGluingRightNerve, ← dgNerve.map_comp]
    rfl
  rel := by
    ext n s
    exact False.elim s.1.2

end SerrePositivity.InfinityCategories
