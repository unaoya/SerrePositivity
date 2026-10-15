module
public import SerrePositivity.CommutativeAlgebra.LocalizationLattice
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.FinitePresentation

/-! # Descent of finite modules along a localization -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits
open scoped ModuleCat.Algebra TensorProduct
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (P : Submonoid R) [IsLocalization P A]

include P in
/-- Finite modules over a localization descend to finitely presented source modules. -/
lemma exists_finitePresentation_descent [IsNoetherianRing R]
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    ∃ M₀ : ModuleCat.{u} R, Module.Finite R M₀ ∧ Module.FinitePresentation R M₀ ∧
      Nonempty (A ⊗[R] M₀ ≃ₗ[A] M) := by
  obtain ⟨L, hL, hloc⟩ := exists_finite_lattice (B := A) P (N := M)
  have : Module.Finite R L := Module.Finite.of_fg hL
  exact ⟨ModuleCat.of R L, inferInstance, Module.finitePresentation_of_finite R L,
    ⟨hloc.tensorEquiv (B := A)⟩⟩

end SerrePositivity
