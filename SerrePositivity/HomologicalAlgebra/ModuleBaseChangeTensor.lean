module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Comparing bundled scalar extension with the algebra tensor product -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open scoped TensorProduct
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- Bridge the bundled scalar extension to the usual algebra tensor product. -/
def moduleCatBaseChangeTensorEquiv (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R B)).obj M ≃ₗ[B] B ⊗[R] M := by
  let φ := algebraMap R B
  have hφ : φ.toAlgebra = (inferInstance : Algebra R B) := toAlgebra_algebraMap
  have e : letI : Algebra R B := φ.toAlgebra
      (ModuleCat.extendScalars φ).obj M ≃ₗ[B] B ⊗[R] M := by
    exact LinearEquiv.refl B _
  rw [hφ] at e
  exact e

end SerrePositivity
