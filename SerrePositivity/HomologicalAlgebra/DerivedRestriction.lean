module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveExactDerived
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Exact restriction of scalars on the standard derived category -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Restriction of scalars on the entire standard derived category. -/
def derivedRestrictScalars :
    DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (ModuleCat.restrictScalars φ).mapDerivedCategory

/-- Derived restriction is computed by ordinary termwise restriction on any complex. -/
def derivedRestrictScalarsFactors :
    DerivedCategory.Q ⋙ derivedRestrictScalars φ ≅
      (ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors

/-- Restriction commutes naturally with homology in all degrees, without boundedness assumptions. -/
def derivedRestrictScalarsHomologyIso (n : ℤ) :
    derivedRestrictScalars φ ⋙ DerivedCategory.homologyFunctor (ModuleCat R) n ≅
      DerivedCategory.homologyFunctor (ModuleCat S) n ⋙ ModuleCat.restrictScalars φ :=
  exactDerivedHomologyNatIso (ModuleCat.restrictScalars φ) n

/-- On single objects, restriction is the standard restriction of the coefficient module. -/
def derivedRestrictScalarsSingleIso (n : ℤ) :
    DerivedCategory.singleFunctor (ModuleCat S) n ⋙ derivedRestrictScalars φ ≅
      ModuleCat.restrictScalars φ ⋙ DerivedCategory.singleFunctor (ModuleCat R) n :=
  (ModuleCat.restrictScalars φ).mapDerivedCategorySingleFunctor n

/-- Restrict the exact scalar restriction functor to the bounded-above categories. -/
def boundedAboveDerivedRestrictScalars :
    DerivedCategory.Minus (ModuleCat.{u} S) ⥤ DerivedCategory.Minus (ModuleCat.{u} R) :=
  boundedAboveExactDerived (ModuleCat.restrictScalars φ)

/-- The bounded version is the restriction of the same functor on the entire derived category. -/
def boundedAboveDerivedRestrictScalarsInclusionIso :
    boundedAboveDerivedRestrictScalars φ ⋙ DerivedCategory.Minus.ι ≅
      DerivedCategory.Minus.ι ⋙ derivedRestrictScalars φ := Iso.refl _

/-- Compute restriction using any specified bounded-above projective model over the larger ring. -/
def boundedAboveDerivedRestrictScalarsModelIso
    (X : DerivedCategory.Minus (ModuleCat.{u} S)) (P : BoundedAboveDerivedModel X.obj) :
    ((boundedAboveDerivedRestrictScalars φ).obj X).obj ≅ DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj P.complex) :=
  boundedAboveExactDerivedModelIso (ModuleCat.restrictScalars φ) X P

end SerrePositivity
