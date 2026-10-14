import SerrePositivity.CommutativeAlgebra.IdempotentImageAnnihilator
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
