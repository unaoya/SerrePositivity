module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient

/-! # Standard completed tensor reduction for arbitrary coefficient modules -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R) (ha : IsSMulRegular R a) (n : ℕ)
    (M N : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing (Ideal.Quotient.mk (Ideal.span {a ^ n})) M)
    (hN : scalarExtensionTorVanishing (Ideal.Quotient.mk (Ideal.span {a ^ n})) N)

/-- Both ordinary residue modules appear with their original quotient actions.
The two Tor conditions are independent; scalar regularity is only required on R. -/
def boundedAboveDerivedCompletedTensorQuotientModuleIso :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ n}))).obj
      ((boundedAboveDerivedCompletionFunctor R a).obj (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N))) ≅
      boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj ((quotientModuleFunctor (Ideal.span {a ^ n})).obj M),
          boundedAboveDerivedSingleFunctor.obj
            ((quotientModuleFunctor (Ideal.span {a ^ n})).obj N)) :=
  (boundedAboveDerivedCompletionQuotientIso R a ha n _).symm ≪≫
    derivedTensorQuotientModuleIso (Ideal.span {a ^ n}) M N hM hN

lemma boundedAboveDerivedCompletedTensorQuotientModuleIso_unit :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a ^ n}))).map
        ((boundedAboveDerivedCompletionUnit R a).app (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N))) ≫
      (boundedAboveDerivedCompletedTensorQuotientModuleIso R a ha n M N hM hN).hom =
        (derivedTensorQuotientModuleIso (Ideal.span {a ^ n}) M N hM hN).hom := by
  change (boundedAboveDerivedCompletionQuotientIso R a ha n _).hom ≫
      ((boundedAboveDerivedCompletionQuotientIso R a ha n _).inv ≫ _) = _
  exact Iso.hom_inv_id_assoc _ _

end SerrePositivity.DerivedCompletion
