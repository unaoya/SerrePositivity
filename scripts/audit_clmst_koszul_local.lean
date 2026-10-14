import SerrePositivity.CommutativeAlgebra.IdempotentImageAnnihilator
import SerrePositivity.HomologicalAlgebra.KoszulTorComparison
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
