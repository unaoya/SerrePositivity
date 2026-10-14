import SerrePositivity.CommutativeAlgebra.LocalizationPowerBound
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
