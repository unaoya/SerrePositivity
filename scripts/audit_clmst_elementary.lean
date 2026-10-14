import SerrePositivity.CommutativeAlgebra.LocalizationPowerBound
import SerrePositivity.CommutativeAlgebra.LocalizationInverse
import SerrePositivity.CommutativeAlgebra.ReducedFiniteFreeIsogeny
import SerrePositivity.HomologicalAlgebra.TwoTermConeAnnihilator
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.exists_uniform_pow_smul_zero
assert_no_sorry SerrePositivity.exists_pow_smul_zero_of_localized_zero
assert_no_sorry SerrePositivity.exists_uniform_pow_smul_zero_of_localization
assert_no_sorry SerrePositivity.awayModuleMap
assert_no_sorry SerrePositivity.exists_pow_smul_mem_range_of_away_surjective
assert_no_sorry SerrePositivity.exists_uniform_pow_smul_coker_zero_of_away_surjective

-- No reducedness, Noetherianity, regularity, or finite presentation is assumed.
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (g : R)
    (h : ∀ x : M, ∃ n : ℕ, g ^ n • x = 0) :
    ∃ n : ℕ, ∀ x : M, g ^ n • x = 0 :=
  SerrePositivity.exists_uniform_pow_smul_zero g h

assert_no_sorry SerrePositivity.exists_clear_denominators
assert_no_sorry SerrePositivity.exists_away_inverse

assert_no_sorry SerrePositivity.mul_eq_zero_of_pow_mul_eq_zero
assert_no_sorry SerrePositivity.smul_eq_zero_of_free_localized_zero
assert_no_sorry SerrePositivity.exists_pow_ker_coker_annihilator

-- In particular the theorem accepts zero g and rank zero.
example {R M : Type*} [CommRing R] [IsReduced R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (f : M →ₗ[R] (Fin 0 → R))
    (hf : Function.Bijective (SerrePositivity.awayModuleMap (0 : R) f)) :
    ∃ a b : ℕ, (∀ x : M, f x = 0 → (0 : R) ^ a • x = 0) ∧
      (∀ y : (Fin 0 → R) ⧸ LinearMap.range f, (0 : R) ^ b • y = 0) :=
  SerrePositivity.exists_pow_ker_coker_annihilator 0 0 f hf

assert_no_sorry SerrePositivity.triangle_scalar_product_eq_zero
assert_no_sorry SerrePositivity.scalar_eq_zero_of_single_homology
assert_no_sorry SerrePositivity.derived_scalar_eq_zero_of_single_cohomology
assert_no_sorry SerrePositivity.two_term_derived_scalar_product_eq_zero
assert_no_sorry SerrePositivity.moduleMapConeComplex_isStrictlyGE
assert_no_sorry SerrePositivity.moduleMapConeComplex_isStrictlyLE
assert_no_sorry SerrePositivity.moduleMapCone_homology_neg_one_scalar_eq_zero
assert_no_sorry SerrePositivity.moduleMapCone_homology_zero_scalar_eq_zero
assert_no_sorry SerrePositivity.moduleMapConeScalar_eq_zero_of_ker_coker_annihilated

-- No projectivity or finiteness is required for the derived cone implication.
example {R M N : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (r s : R)
    (hr : ∀ x : M, f x = 0 → r • x = 0)
    (hs : ∀ y : N ⧸ f.range, s • y = 0) :
    SerrePositivity.moduleMapConeScalar R f (r * s) = 0 :=
  SerrePositivity.moduleMapConeScalar_eq_zero_of_ker_coker_annihilated R f r s hr hs
