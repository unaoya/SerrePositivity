module
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient

/-! # Ordinary residue factors in completed tensor base change under explicit regularity -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable (R : Type u) [CommRing R] (a : R) (ha : IsSMulRegular R a) (n : ℕ)
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (hS : IsSMulRegular S a) (hT : IsSMulRegular T a)
local notation "q" => Ideal.Quotient.mk (Ideal.span {a ^ n})

/-- Regularity of both factors supplies both independent Tor inputs in completed base change. -/
def regularCompletedTensorQuotientAlgebraIso :
    (boundedAboveDerivedBaseChange (q)).obj ((boundedAboveDerivedCompletionFunctor R a).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S),
            boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))) ≅
      boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj
          (ModuleCat.of (R ⧸ Ideal.span {a ^ n})
            (S ⧸ Ideal.map (algebraMap R S) (Ideal.span {a ^ n}))),
          boundedAboveDerivedSingleFunctor.obj
            (ModuleCat.of (R ⧸ Ideal.span {a ^ n})
              (T ⧸ Ideal.map (algebraMap R T) (Ideal.span {a ^ n})))) :=
  boundedAboveDerivedCompletedTensorQuotientAlgebraIso R a ha n S T
    (scalarExtensionTorVanishing_principal_pow_of_regular a ha (ModuleCat.of R S) hS n)
    (scalarExtensionTorVanishing_principal_pow_of_regular a ha (ModuleCat.of R T) hT n)

/-- The comparison after the image of the original completion unit is standard base change. -/
lemma regularCompletedTensorQuotientAlgebraIso_unit :
    (boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R a).app
          (boundedAboveDerivedTensor.obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S),
              boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))) ≫
      (regularCompletedTensorQuotientAlgebraIso R a ha n S T hS hT).hom =
    (derivedTensorQuotientAlgebraIso (Ideal.span {a ^ n}) S T
      (scalarExtensionTorVanishing_principal_pow_of_regular a ha (ModuleCat.of R S) hS n)
      (scalarExtensionTorVanishing_principal_pow_of_regular a ha (ModuleCat.of R T) hT n)).hom := by
  change (boundedAboveDerivedCompletionQuotientIso R a ha n _).hom ≫
      ((boundedAboveDerivedCompletionQuotientIso R a ha n _).inv ≫ _) = _
  exact Iso.hom_inv_id_assoc _ _

end SerrePositivity.DerivedCompletion
