module

public import SerrePositivity.KTheory.CoefficientExtension

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

/-- Coefficient-linear maps are determined by the original integral classes. -/
lemma coefficientLinearMap_ext (F G : E ⊗[ℤ] A →ₗ[E] B)
    (h : ∀ x, F ((1 : E) ⊗ₜ[ℤ] x) = G ((1 : E) ⊗ₜ[ℤ] x)) : F = G := by
  apply AlgebraTensorModule.ext
  intro a x
  rw [TensorProduct.tmul_eq_smul_one_tmul a, F.map_smul, G.map_smul, h]

lemma coefficientLinearExtension_unique (f : A →+ B) (F : E ⊗[ℤ] A →ₗ[E] B)
    (hF : ∀ x, F ((1 : E) ⊗ₜ[ℤ] x) = f x) : F = coefficientLinearExtension E f := by
  apply coefficientLinearMap_ext E
  simpa only [coefficientLinearExtension_tmul, one_smul] using hF

end SerrePositivity
