module
public import SerrePositivity.HomologicalAlgebra.DerivedRestrictionNormalization

/-! # The original single H⁰ normalization under exact derived restriction -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory HomologicalComplex CategoryTheory.Functor
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Compute the original derived homology restriction comparison on a represented complex. -/
lemma derivedRestrictionHomologyIso_factors (K : CochainComplex (ModuleCat S) ℤ) (n : ℤ) :
    (derivedRestrictScalarsHomologyIso φ n).hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctor (ModuleCat R) n).map
          ((derivedRestrictScalarsFactors φ).hom.app K) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat R) n).hom.app
          (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (K.sc n |>.mapHomologyIso (ModuleCat.restrictScalars φ)).hom ≫
        (ModuleCat.restrictScalars φ).map
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) n).inv.app K) := by
  simp [derivedRestrictScalarsHomologyIso, exactDerivedHomologyNatIso,
    Localization.liftNatIso_hom, Localization.liftNatTrans_app, Localization.Lifting.iso,
    exactCochainHomologyIso, derivedRestrictScalarsFactors]

/-- The original derived single and homology restriction comparisons use the same H⁰ class. -/
lemma derivedRestrictionSingleH0_normalization (M : ModuleCat S) :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((derivedRestrictScalarsSingleIso φ 0).hom.app M) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
        ((ModuleCat.restrictScalars φ).obj M) =
    (derivedRestrictScalarsHomologyIso φ 0).hom.app
        ((DerivedCategory.singleFunctor (ModuleCat S) 0).obj M) ≫
      (ModuleCat.restrictScalars φ).map
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat S) 0).hom.app M) := by
  apply (cancel_epi ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    ((derivedRestrictScalarsFactors φ).inv.app
      ((CochainComplex.singleFunctor (ModuleCat S) 0).obj M)))).mp
  rw [← CategoryTheory.Functor.map_comp_assoc]
  erw [mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app
      (ModuleCat.restrictScalars φ) M]
  rw [derivedSingleH0Iso_formula]
  rw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]
  erw [restrictionSingleHomologyIso φ M]
  erw [derivedRestrictionHomologyIso_factors]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← CategoryTheory.Functor.map_comp]
  rw [derivedSingleH0Iso_formula]
  simp only [Iso.inv_hom_id_app_assoc]

end SerrePositivity
