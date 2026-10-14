module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorBaseChange
public import SerrePositivity.HomologicalAlgebra.TensorSingleNaturality

/-! # Scalar extension followed by restriction as an ordinary tensor complex -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- The larger ring as a module over the original ring. -/
abbrev baseChangeScalarModule : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)

/-- Restrict the scalar-extended complex and identify it with the single-module tensor. -/
def restrictedBaseChangeComplexIso (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj (baseChange φ P) ≅
      cochainTensor (cochainSingleZero (baseChangeScalarModule φ)) P :=
  (Functor.mapHomologicalComplexCompIso (extendRestrictTensorIso φ) (.up ℤ)).app P ≪≫
    (cochainTensorSingleLeftIso (baseChangeScalarModule φ) P).symm

/-- The comparison respects every chain map, including the unreplaced scalar module. -/
lemma restrictedBaseChangeComplexIso_naturality
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map f) ≫
        (restrictedBaseChangeComplexIso φ Q).hom =
      (restrictedBaseChangeComplexIso φ P).hom ≫
        cochainTensorMap (𝟙 (cochainSingleZero (baseChangeScalarModule φ))) f := by
  apply (cancel_mono (cochainTensorSingleLeftIso (baseChangeScalarModule φ) Q).hom).mp
  simp only [restrictedBaseChangeComplexIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [cochainTensorSingleLeftIso_naturality]
  simp only [Iso.inv_hom_id_assoc]
  exact (Functor.mapHomologicalComplexCompIso (extendRestrictTensorIso φ) (.up ℤ)).hom.naturality f

end SerrePositivity
