module
public import SerrePositivity.KST.Fibration.DGNuMultiRealization
public import SerrePositivity.KST.SConstruction.StableBoundaryPointedFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryPointedFunctor
public import SerrePositivity.KST.Fibration.CofiberFamilyPrecompose

/-! # 元の境界商の全基点固定族を、同じ ν の後合成として照合する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A]

/-- 同じ元の境界商・商射・基点を保つ全 Hom 族は、ν の後合成と厳密に一致。 -/
theorem dgNuBoundaryFamily_map (r : ℕ) (P Q : PerfDGInput.{u, v} A) :
    (presentedPerfectDGEnrichedExactFunctor A).map P Q ≫
      stableBoundaryReducedFamilyMap r
        (presentedPerfectDGStableQCat A P) (presentedPerfectDGStableQCat A Q) =
      presentedPerfectDGBoundaryReducedFamilyMap A r P Q := by
  apply cofiberFamilyDesc_precompose
  have ha := congrArg (uncurry (C := SSet.{max (u + 1) v}))
    (dgNuMultiRealization_map A (r + 1) P Q)
  rw [uncurry_natural_left] at ha
  rw [← Category.assoc]
  exact congrArg (fun g => g ≫ boundaryReductionQuotient r
    (stableCategoryModel (presentedPerfectDGStableQCat A Q))) ha

end SerrePositivity.KST.Fibration
