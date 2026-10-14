import SerrePositivity.CommutativeAlgebra.LocalizationPowerBound
import SerrePositivity.CommutativeAlgebra.LocalizationInverse
import SerrePositivity.CommutativeAlgebra.ReducedFiniteFreeIsogeny
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
