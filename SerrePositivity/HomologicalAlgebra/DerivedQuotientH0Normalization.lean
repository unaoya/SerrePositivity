module
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientBaseChange
public import SerrePositivity.HomologicalAlgebra.RealizedSingleH0Normalization

/-! # The original derived quotient H⁰ comparison and its standard representative classes -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (I : Ideal R)
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk I

/-- H⁰ of the original derived quotient is the usual residue module, without a Tor hypothesis. -/
def quotientBaseChangeH0Iso (M : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor (ModuleCat (R ⧸ I)) 0).obj
        ((boundedAboveDerivedBaseChange (q)).obj (boundedAboveDerivedSingleFunctor.obj M)).obj ≅
      (quotientModuleFunctor I).obj M :=
  (boundedAboveDerivedBaseChangeModuleH0Iso (q)).app M ≪≫
    (quotientScalarExtensionEquiv I M).toModuleIso

/-- The Tor-vanishing augmentation induces exactly this original standard H⁰ comparison. -/
lemma derivedQuotientModuleIso_homology (M : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing (q) M) :
    (DerivedCategory.homologyFunctor (ModuleCat (R ⧸ I)) 0).map
        (derivedQuotientModuleIso I M hM).hom.hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat (R ⧸ I)) 0).hom.app
          ((quotientModuleFunctor I).obj M) =
      (quotientBaseChangeH0Iso I M).hom := by
  let H0 := DerivedCategory.homologyFunctor (ModuleCat (R ⧸ I)) 0
  let e := (quotientScalarExtensionEquiv I M).toModuleIso
  let σ := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat (R ⧸ I)) 0
  let β := (boundedAboveDerivedBaseChangeModuleAugmentation (q)).app M
  have hn := σ.hom.naturality e.hom
  change H0.map ((DerivedCategory.singleFunctor (ModuleCat (R ⧸ I)) 0).map e.hom) ≫
      σ.hom.app _ = σ.hom.app _ ≫ e.hom at hn
  change H0.map (β ≫
      (DerivedCategory.singleFunctor (ModuleCat (R ⧸ I)) 0).map e.hom) ≫
      σ.hom.app _ = (boundedAboveDerivedBaseChangeModuleH0Iso (q)).hom.app M ≫ e.hom
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc]
  have h := boundedAboveDerivedBaseChangeModuleAugmentation_homology (q) M
  rw [realizedSingleH0Iso_hom_eq_standard] at h
  exact congrArg (fun k => k ≫ e.hom) h

/-- The original class of 1 tensor m goes to the original residue class of m. -/
lemma quotientBaseChangeH0Iso_one_tmul (M : ModuleCat.{u} R) (m : M) :
    (quotientBaseChangeH0Iso I M).hom
        ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app M
          ((1 : R ⧸ I) ⊗ₜ[R, Ideal.Quotient.mk I] m)) =
      (I • (⊤ : Submodule R M)).mkQ m := by
  let e := (boundedAboveDerivedBaseChangeModuleH0Iso (q)).app M
  change quotientScalarExtensionEquiv I M
      (e.hom (e.inv ((1 : R ⧸ I) ⊗ₜ[R, Ideal.Quotient.mk I] m))) = _
  rw [show e.hom (e.inv ((1 : R ⧸ I) ⊗ₜ[R, Ideal.Quotient.mk I] m)) =
      (1 : R ⧸ I) ⊗ₜ[R, Ideal.Quotient.mk I] m from e.toLinearEquiv.apply_symm_apply _]
  exact quotientScalarExtensionEquiv_one_tmul I M m

end SerrePositivity
