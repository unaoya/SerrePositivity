module
public import SerrePositivity.KTheory.Coefficients
public import SerrePositivity.PerfectComplex.IntegerEuler

/-! # Euler evaluation after extension of supported K₀ coefficients -/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity
open TensorProduct
variable (E : Type v) [CommRing E] (R : Type u) [CommRing R]
namespace K0WithSupport
variable [IsNoetherianRing R] [IsLocalRing R]

/-- The integer Euler map followed by extension of coefficients and E ⊗ ℤ ≃ E. -/
def coefficientEuler : Coefficients E (supportZeroLocus (IsLocalRing.maximalIdeal R)) →ₗ[E] E :=
  (AlgebraTensorModule.rid ℤ E E).toLinearMap ∘ₗ g0CoefficientMap E (integerEuler R)

@[simp]
lemma coefficientEuler_tmul (a : E)
    (x : K0WithSupport (supportZeroLocus (IsLocalRing.maximalIdeal R))) :
    coefficientEuler E R (a ⊗ₜ[ℤ] x) = a * (integerEuler R x : E) := by
  simp only [coefficientEuler, LinearMap.comp_apply, g0CoefficientMap_tmul,
    LinearEquiv.coe_coe, AlgebraTensorModule.rid_tmul, zsmul_eq_mul, mul_comm]

/-- Vanishing after characteristic-zero coefficient extension forces
the integer Euler value to zero. -/
lemma integerEuler_eq_zero_of_one_tmul_eq_zero [CharZero E]
    (x : K0WithSupport (supportZeroLocus (IsLocalRing.maximalIdeal R)))
    (hx : (1 : E) ⊗ₜ[ℤ] x = 0) : integerEuler R x = 0 := by
  have he := congrArg (coefficientEuler E R) hx
  simp only [coefficientEuler_tmul, one_mul, map_zero] at he
  exact_mod_cast he

end K0WithSupport
end SerrePositivity
