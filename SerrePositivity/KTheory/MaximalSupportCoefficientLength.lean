module

public import SerrePositivity.KTheory.MaximalSupportLengthEquiv
public import SerrePositivity.KTheory.G0Coefficients
public import SerrePositivity.KTheory.CoefficientLinearExtension
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Coefficient length coordinates for G₀ on finite maximal support -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
open TensorProduct IsLocalRing
namespace Adams
variable (E : Type v) [CommRing E] {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (W : TopologicalSpace.Closeds (PrimeSpectrum R))
variable (hw : ∀ p ∈ W, p.asIdeal.IsMaximal)
variable [Fintype {p : PrimeSpectrum R // p ∈ W}]

def coefficientG0LengthEquiv : G0WithSupport.Coefficients E W ≃ₗ[E]
    ({p : PrimeSpectrum R // p ∈ W} → E) := by
  classical
  exact ((maximalLengthEquiv W hw).toIntLinearEquiv.baseChange ℤ E _ _) ≪≫ₗ
    TensorProduct.piScalarRight ℤ E E {p : PrimeSpectrum R // p ∈ W}

lemma coefficientG0LengthEquiv_tmul (a : E) (x : G0WithSupport W)
    (p : {p : PrimeSpectrum R // p ∈ W}) :
    coefficientG0LengthEquiv E W hw (a ⊗ₜ[ℤ] x) p =
      a * (localLengthMap W hw p.val x : E) := by
  classical
  change (TensorProduct.piScalarRightHom ℤ E E _
    (a ⊗ₜ[ℤ] maximalLengthEvaluation W hw x)) p = _
  rw [TensorProduct.piScalarRightHom_tmul]
  simp only [maximalLengthEvaluation_apply, zsmul_eq_mul, mul_comm]

end Adams
end SerrePositivity
