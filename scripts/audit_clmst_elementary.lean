import SerrePositivity.CommutativeAlgebra.LocalizationPowerBound
import SerrePositivity.CommutativeAlgebra.LocalizationInverse
import SerrePositivity.CommutativeAlgebra.ReducedFiniteFreeIsogeny
import SerrePositivity.HomologicalAlgebra.TwoTermConeAnnihilator
import SerrePositivity.CLMST.FiniteFreeConeIsogeny
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

assert_no_sorry SerrePositivity.CLMST.finiteFreeConeIsogeny
assert_no_sorry SerrePositivity.CLMST.finiteFreeConeIsogeny_with_annihilators
assert_no_sorry SerrePositivity.CLMST.finiteAlgebraConeIsogeny

open SerrePositivity

-- The final cone theorem allows both g = 0 and free rank = 0.
example {R M : Type} [CommRing R] [IsReduced R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (f : M →ₗ[R] (Fin 0 → R))
    (hf : Function.Bijective (awayModuleMap (0 : R) f)) :
    ∃ n : ℕ, moduleMapConeScalar R f ((0 : R) ^ n) = 0 :=
  CLMST.finiteFreeConeIsogeny R 0 0 f hf

-- Multiplication by the zero divisor g=(1,0) is not injective before localization.
example : ∃ n : ℕ, moduleMapConeScalar (ℤ × ℤ)
    (((1, 0) : ℤ × ℤ) •
      (LinearMap.id : (Fin 1 → ℤ × ℤ) →ₗ[ℤ × ℤ] (Fin 1 → ℤ × ℤ)))
    ((1, 0) ^ n) = 0 := by
  apply CLMST.finiteFreeConeIsogeny (ℤ × ℤ) (1, 0) 1
  let ι := LocalizedModule.mkLinearMap (Submonoid.powers ((1, 0) : ℤ × ℤ))
    (Fin 1 → ℤ × ℤ)
  have hb := (Module.End.isUnit_iff _).mp
    (IsLocalizedModule.Away.isUnit_algebraMap ι ((1, 0) : ℤ × ℤ))
  change Function.Bijective (fun x ↦ ((1, 0) : ℤ × ℤ) • x) at hb
  simp only [awayModuleMap, map_smul, IsLocalizedModule.map_id]
  change Function.Bijective (fun x ↦ ((1, 0) : ℤ × ℤ) • x)
  exact hb

-- The zero module is the rank-zero free module.
example : ∃ n : ℕ, moduleMapConeScalar ℤ
    (LinearMap.id : (Fin 0 → ℤ) →ₗ[ℤ] (Fin 0 → ℤ)) (0 ^ n) = 0 := by
  apply CLMST.finiteFreeConeIsogeny ℤ 0 0 LinearMap.id
  simpa only [awayModuleMap, IsLocalizedModule.map_id, LinearMap.id_coe] using
    (Function.bijective_id : Function.Bijective
      (id : LocalizedModule (Submonoid.powers (0 : ℤ)) (Fin 0 → ℤ) → _))

-- Consistency with the existing implication from a cone zero morphism to annihilators.
example {R M : Type} [CommRing R] [IsReduced R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (g : R) (r : ℕ) (f : M →ₗ[R] (Fin r → R))
    (hf : Function.Bijective (awayModuleMap g f)) :
    ∃ n : ℕ, moduleMapConeScalar R f (g ^ n) = 0 ∧
      (∀ x : f.ker, g ^ n • x = 0) ∧
      (∀ y : (Fin r → R) ⧸ f.range, g ^ n • y = 0) :=
  CLMST.finiteFreeConeIsogeny_with_annihilators R g r f hf
