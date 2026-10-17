import SerrePositivity.CommutativeAlgebra.BoundedPowerTorsionQuotient
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.isSMulRegular_quotient_pow_kernel
assert_no_sorry SerrePositivity.bounded_power_torsion_decomposition
#print axioms SerrePositivity.isSMulRegular_quotient_pow_kernel
#print axioms SerrePositivity.bounded_power_torsion_decomposition

universe u
open SerrePositivity

-- a = 0 and arbitrary M: the regular quotient is the actual zero quotient.
theorem audit_prop247_bounded_zero_scalar
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    IsSMulRegular (M ⧸ ((0 : R) ^ 1 • (LinearMap.id : M →ₗ[R] M)).ker) (0 : R) := by
  apply isSMulRegular_quotient_pow_kernel (0 : R) 1
  intro n x _hx
  simp

assert_no_sorry audit_prop247_bounded_zero_scalar
#print axioms audit_prop247_bounded_zero_scalar
