import SerrePositivity.HomologicalAlgebra.DerivedQuotientTensorAugmentation
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.quotientTensorScalarExtensionMap
assert_no_sorry SerrePositivity.quotientTensorScalarExtensionMap_one_tmul
assert_no_sorry SerrePositivity.derivedTensorQuotientAlgebraIso_augmentation
assert_no_sorry SerrePositivity.quotientTensorScalarExtensionMap_isIso
assert_no_sorry SerrePositivity.derivedTensorQuotientAlgebraIso_homology
assert_no_sorry SerrePositivity.derivedTensorQuotientAugmentation_h0_isIso
assert_no_sorry SerrePositivity.derivedTensorQuotientBaseChangeH0Iso
assert_no_sorry SerrePositivity.derivedTensorQuotientAlgebraIso_homology_tmul

#print axioms SerrePositivity.quotientTensorScalarExtensionMap
#print axioms SerrePositivity.quotientTensorScalarExtensionMap_one_tmul
#print axioms SerrePositivity.derivedTensorQuotientAlgebraIso_augmentation
#print axioms SerrePositivity.quotientTensorScalarExtensionMap_isIso
#print axioms SerrePositivity.derivedTensorQuotientAlgebraIso_homology
#print axioms SerrePositivity.derivedTensorQuotientAugmentation_h0_isIso
#print axioms SerrePositivity.derivedTensorQuotientBaseChangeH0Iso
#print axioms SerrePositivity.derivedTensorQuotientAlgebraIso_homology_tmul

noncomputable section
universe u
open CategoryTheory SerrePositivity
open scoped TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable (R : Type u) [CommRing R] (I : Ideal R) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
set_option quotPrecheck false in
local notation "Q" => R ⧸ I
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk I
set_option quotPrecheck false in
local notation "SQ" => S ⧸ I.map (algebraMap R S)
set_option quotPrecheck false in
local notation "TQ" => T ⧸ I.map (algebraMap R T)

-- Ordinary comparison uses no Tor input, even at a zero source representative.
example (t : T) :
    quotientTensorScalarExtensionMap I S T
        ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk I] ((0 : S) ⊗ₜ[R] t)) = 0 := by
  rw [quotientTensorScalarExtensionMap_one_tmul, map_zero, TensorProduct.zero_tmul]

-- The normalized actual derived class has the same zero right-factor image.
example (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T)) (s : S) :
    letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ)
    letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ)
    derivedTensorH0AlgEquiv (R := Q) SQ TQ
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          (derivedTensorQuotientAlgebraIso I S T hS hT).hom.hom
          ((derivedTensorQuotientBaseChangeH0Iso I S T hS hT).inv
            ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk I] (s ⊗ₜ[R] (0 : T))))) = 0 := by
  let := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ)
  let := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ)
  rw [derivedTensorQuotientAlgebraIso_homology_tmul, map_zero, TensorProduct.tmul_zero]

-- The top ideal is permitted; the quotient coefficient ring can be the zero ring.
example (s : S) (t : T) :
    quotientTensorScalarExtensionMap (⊤ : Ideal R) S T
        ((1 : R ⧸ (⊤ : Ideal R)) ⊗ₜ[R, Ideal.Quotient.mk (⊤ : Ideal R)] (s ⊗ₜ[R] t)) =
      Ideal.Quotient.mk ((⊤ : Ideal R).map (algebraMap R S)) s ⊗ₜ[R ⧸ (⊤ : Ideal R)]
        Ideal.Quotient.mk ((⊤ : Ideal R).map (algebraMap R T)) t :=
  quotientTensorScalarExtensionMap_one_tmul (⊤ : Ideal R) S T s t
