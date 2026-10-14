module

public import SerrePositivity.KTheory.LocalizationCoefficients

/-! # Extending an additive map into a coefficient module -/

@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity
open TensorProduct
variable (E : Type v) [CommRing E]
variable {A : Type u} [AddCommGroup A] {B : Type w} [AddCommGroup B] [Module E B]

/-- Extend an additive map to the coefficient tensor product, with its target already E-linear. -/
def coefficientLinearExtension (f : A →+ B) : E ⊗[ℤ] A →ₗ[E] B :=
  AlgebraTensorModule.lift ((LinearMap.id : E →ₗ[E] E).smulRight f.toIntLinearMap)

@[simp]
lemma coefficientLinearExtension_tmul (f : A →+ B) (a : E) (x : A) :
    coefficientLinearExtension E f (a ⊗ₜ[ℤ] x) = a • f x := rfl

lemma coefficientLinearExtension_unique (f : A →+ B) (F : E ⊗[ℤ] A →ₗ[E] B)
    (hF : ∀ x, F ((1 : E) ⊗ₜ[ℤ] x) = f x) : F = coefficientLinearExtension E f := by
  apply AlgebraTensorModule.ext
  intro a x
  have h : a ⊗ₜ[ℤ] x = a • ((1 : E) ⊗ₜ[ℤ] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  calc
    F (a ⊗ₜ[ℤ] x) = a • F ((1 : E) ⊗ₜ[ℤ] x) := by rw [h, F.map_smul]
    _ = a • f x := congrArg (fun y => a • y) (hF x)
    _ = coefficientLinearExtension E f (a ⊗ₜ[ℤ] x) := rfl

end SerrePositivity
