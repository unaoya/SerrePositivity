import SerrePositivity.CommutativeAlgebra.IdempotentImageAnnihilator
import SerrePositivity.HomologicalAlgebra.KoszulTorComparison
import SerrePositivity.HomologicalAlgebra.KoszulTensorConeComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.ideal_le_pow_sup_of_quotient_image_idempotent
assert_no_sorry SerrePositivity.smul_eq_zero_of_ideal_pow_and_quotient_image_idempotent
assert_no_sorry SerrePositivity.ideal_annihilates_of_pow_annihilates_mod
assert_no_sorry SerrePositivity.ideal_annihilates_of_pow_annihilates_and_principal_torsion
assert_no_sorry SerrePositivity.ideal_annihilates_of_pow_annihilates_and_powerTorsion

open SerrePositivity

-- Arbitrary modules, possibly with no uniform torsion exponent.
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (a : R)
    (hI : ∀ n : ℕ, 0 < n → IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (hpow : ∀ r ∈ I ^ 3, ∀ x : M, r • x = 0)
    (ht : ∀ x : M, ∃ n : ℕ, a ^ n • x = 0) : ∀ r ∈ I, ∀ x : M, r • x = 0 :=
  ideal_annihilates_of_pow_annihilates_and_powerTorsion I a hI 3 (by omega) hpow ht

-- No regularity of a, primeness, or positivity of the torsion exponent is needed here.
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (a : R) (n : ℕ)
    (hI : IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (hpow : ∀ r ∈ I ^ 2, ∀ x : M, r • x = 0) (ht : ∀ x : M, a ^ n • x = 0) :
    ∀ r ∈ I, ∀ x : M, r • x = 0 :=
  ideal_annihilates_of_pow_annihilates_and_principal_torsion I a n hI 2 (by omega) hpow ht

#print axioms SerrePositivity.ideal_annihilates_of_pow_annihilates_and_powerTorsion

-- KL1a: the coefficient tensor model and natural Tor comparison.
assert_no_sorry SerrePositivity.koszulTensorModuleFunctor
assert_no_sorry SerrePositivity.koszulTensorModuleHomologyFunctor
assert_no_sorry SerrePositivity.koszulTorComparison
assert_no_sorry SerrePositivity.koszulTorComparisonEquiv
assert_no_sorry SerrePositivity.koszulTorComparison_naturality
assert_no_sorry SerrePositivity.koszulTorComparison_map_eq_zero_iff
assert_no_sorry SerrePositivity.torCoefficientScalarEndomorphism
assert_no_sorry SerrePositivity.koszulTensorCoefficientScalarEndomorphism
assert_no_sorry SerrePositivity.koszulTorComparison_coefficient_scalar
assert_no_sorry SerrePositivity.koszulTensorCoefficientScalar_eq_zero_iff
assert_no_sorry SerrePositivity.koszulTensorCoefficientScalar_eq_zero_of_tor_annihilated
assert_no_sorry SerrePositivity.koszulTorPowersComparison

open CategoryTheory
noncomputable section
-- No completeness, flatness, finite generation, or algebra structure on the test module.
example (R : Type) [CommRing R] {n : ℕ} (z : Fin n → R) (hz : IsKoszulResolution z)
    (i : ℕ) (M : ModuleCat.{0} R) :
    ((koszulTensorModuleFunctor z).obj M).homology (-(i : ℤ)) ≃ₗ[R]
      ((Tor (ModuleCat.{0} R) i).obj M).obj (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) :=
  koszulTorComparisonEquiv z hz i M

#print axioms SerrePositivity.koszulTorComparison
#print axioms SerrePositivity.koszulTorComparison_coefficient_scalar
#print axioms SerrePositivity.koszulTorPowersComparison

-- KL1b: cone comparison, coefficient actions, and the coefficient transition maps.
assert_no_sorry SerrePositivity.additiveFunctorCofiberIsoOfEq
assert_no_sorry SerrePositivity.additiveFunctorCofiberIsoOfEq_inv_inl
assert_no_sorry SerrePositivity.additiveFunctorCofiberIsoOfEq_inv_inr
assert_no_sorry SerrePositivity.linearFunctorScalarConeIso
assert_no_sorry SerrePositivity.linearFunctorScalarConeIso_natTrans
assert_no_sorry SerrePositivity.koszulTensorConeIso
assert_no_sorry SerrePositivity.koszulTensorConeIso_naturality
assert_no_sorry SerrePositivity.koszulTensorConeNatIso
assert_no_sorry SerrePositivity.koszulModuleTorComparison
assert_no_sorry SerrePositivity.koszulTensorCoefficientMapOfComplexMap
assert_no_sorry SerrePositivity.koszulModuleCoefficientMapOfComplexMap
assert_no_sorry SerrePositivity.koszulTensorConeNatIso_complex_map_compatibility
assert_no_sorry SerrePositivity.koszulModuleCoefficientMapOfComplexMap_id
assert_no_sorry SerrePositivity.koszulModuleCoefficientMapOfComplexMap_comp
assert_no_sorry SerrePositivity.powerKoszulModuleTransition
assert_no_sorry SerrePositivity.koszulTensorConeNatIso_power_transition
assert_no_sorry SerrePositivity.koszulModuleTorComparison_naturality
assert_no_sorry SerrePositivity.koszulModuleTorComparison_map_eq_zero_iff
assert_no_sorry SerrePositivity.koszulModuleHomology_coefficient_scalar_eq_zero_of_tor_annihilated
assert_no_sorry SerrePositivity.koszulModuleTorPowersComparison

-- Arbitrary module maps, including endomorphisms coming from a coefficient algebra.
example (R : Type) [CommRing R] {n : ℕ} (z : Fin n → R)
    (M N : ModuleCat.{0} R) (f : M ⟶ N) :
    (koszulTensorModuleFunctor z).map f ≫ (koszulTensorConeIso z N).hom =
      (koszulTensorConeIso z M).hom ≫ (koszulModuleFunctor z).map f :=
  koszulTensorConeIso_naturality z f

-- The zero stage of the power tower is allowed; no regular sequence assumption is needed.
example (R : Type) [CommRing R] {n : ℕ} (z : Fin n → R) :
    koszulModuleFunctor (fun j ↦ z j ^ 1) ⟶ koszulModuleFunctor (fun j ↦ z j ^ 0) :=
  powerKoszulModuleTransition z 0

#print axioms SerrePositivity.linearFunctorScalarConeIso_natTrans
#print axioms SerrePositivity.koszulTensorConeIso_naturality
#print axioms SerrePositivity.koszulModuleTorComparison
#print axioms SerrePositivity.koszulTensorConeNatIso_power_transition
