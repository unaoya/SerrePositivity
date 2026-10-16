module
public import SerrePositivity.HomologicalAlgebra.DerivedRestriction
public import SerrePositivity.HomologicalAlgebra.UnitHomologyNormalization

/-! # Normalize exact restriction comparisons on standard single H⁰ classes -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- The exact homology comparison preserves the original homology projection. -/
lemma restrictionHomologyIso_projection (K : CochainComplex (ModuleCat S) ℤ) (n : ℤ) :
    (K.sc n |>.map (ModuleCat.restrictScalars φ)).homologyπ ≫
        (K.sc n |>.mapHomologyIso (ModuleCat.restrictScalars φ)).hom =
      (K.sc n |>.mapCyclesIso (ModuleCat.restrictScalars φ)).hom ≫
        (ModuleCat.restrictScalars φ).map (K.homologyπ n) := by
  let F := ModuleCat.restrictScalars φ
  let h := (K.sc n).homologyData.left
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [(h.map F).homologyπ_comp_homologyIso_hom_assoc]
  change _ ≫ F.map h.π ≫ F.map h.homologyIso.inv = _
  rw [← CategoryTheory.Functor.map_comp, h.π_comp_homologyIso_inv,
    CategoryTheory.Functor.map_comp]
  rfl

/-- On a single complex, exact restriction preserves its original H⁰ class identification. -/
lemma restrictionSingleHomologyIso (M : ModuleCat S) :
    HomologicalComplex.homologyMap
        (((ModuleCat.restrictScalars φ).mapCochainComplexSingleFunctor 0).hom.app M) 0 ≫
      (singleObjHomologySelfIso (.up ℤ) 0
        ((ModuleCat.restrictScalars φ).obj M)).hom =
    (((single (ModuleCat S) (.up ℤ) 0).obj M).sc 0 |>.mapHomologyIso
      (ModuleCat.restrictScalars φ)).hom ≫
      (ModuleCat.restrictScalars φ).map (singleObjHomologySelfIso (.up ℤ) 0 M).hom := by
  apply (cancel_epi ((((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
    ((single (ModuleCat S) (.up ℤ) 0).obj M)).homologyπ 0)).mp
  rw [homologyπ_naturality_assoc]
  erw [homologyπ_singleObjHomologySelfIso_hom]
  erw [reassoc_of% restrictionHomologyIso_projection φ
    ((single (ModuleCat S) (.up ℤ) 0).obj M) 0]
  rw [singleObjCyclesSelfIso_hom]
  rw [← CategoryTheory.Functor.map_comp]
  rw [homologyπ_singleObjHomologySelfIso_hom]
  rw [singleObjCyclesSelfIso_hom, CategoryTheory.Functor.map_comp, ← Category.assoc]
  erw [CategoryTheory.ShortComplex.mapCyclesIso_hom_iCycles]
  erw [cyclesMap_i]
  rw [Category.assoc]
  simp only [CategoryTheory.Functor.mapCochainComplexSingleFunctor,
    singleMapHomologicalComplex_hom_app_self, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end SerrePositivity
