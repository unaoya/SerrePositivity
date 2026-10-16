module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorLinear
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedModule
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionTensorComparison

/-! # Tensoring completion equivalences with actual power-torsion derived objects

The comparison is the original tensor of the given morphism. No regularity,
flatness, finite generation, or completeness of the left factor is assumed.
-/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- A power killing a derived tensor factor kills the same power on the whole tensor. -/
lemma derivedTensor_scalar_pow_zero_right (X Y : D) (n : ℕ)
    (hY : a ^ n • 𝟙 Y = 0) : a ^ n • 𝟙 (X ⊗ Y) = 0 := by
  calc
    a ^ n • 𝟙 (X ⊗ Y) = (𝟙 X) ⊗ₘ (a ^ n • 𝟙 Y) := by
      rw [derivedTensorHom_smul_right, id_tensorHom_id]
    _ = 0 := by rw [hY]; simp

/-- The tensor is complete because its actual identity has a power-torsion scalar action. -/
lemma derivedTensor_isComplete_of_right_scalar_pow_zero (X Y : D) (n : ℕ)
    (hY : a ^ n • 𝟙 Y = 0) : IsComplete R a (X ⊗ Y).obj := by
  apply isComplete_of_scalar_pow_zero R a _ n
  exact congrArg (fun f : X ⊗ Y ⟶ X ⊗ Y => f.hom)
    (derivedTensor_scalar_pow_zero_right R a X Y n hY)

/-- A completion equivalence becomes an actual isomorphism after tensoring with a
power-torsion derived object; the original morphism is retained. -/
lemma completionEquivalence_tensor_powerTorsion_isIso {X X' : D} (f : X ⟶ X')
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f.hom))
    (Y : D) (n : ℕ) (hY : a ^ n • 𝟙 Y = 0) : IsIso (f ▷ Y) := by
  have h := completionEquivalence_whiskerRight R a f hf Y
  apply boundedAbove_isIso_of_koszul_of_isComplete R a (f ▷ Y)
    (derivedTensor_isComplete_of_right_scalar_pow_zero R a X Y n hY)
    (derivedTensor_isComplete_of_right_scalar_pow_zero R a X' Y n hY)
  exact fun k => derivedScalarCone_map_isIso_of_completion R a (f ▷ Y).hom h k

/-- In particular the original completion unit is inverted by a power-torsion tensor test. -/
lemma completionUnit_tensor_powerTorsion_isIso (X Y : D) (n : ℕ)
    (hY : a ^ n • 𝟙 Y = 0) :
    IsIso ((boundedAboveDerivedCompletionUnit R a).app X ▷ Y) :=
  completionEquivalence_tensor_powerTorsion_isIso R a _
    (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj) Y n hY

/-- Arbitrary power-torsion module tests invert the same original completion unit. -/
lemma completionUnit_tensor_module_powerTorsion_isIso (X : D) (N : ModuleCat.{u} R)
    (n : ℕ) (hN : ∀ x : N, a ^ n • x = 0) :
    IsIso ((boundedAboveDerivedCompletionUnit R a).app X ▷
      boundedAboveDerivedSingleFunctor.obj N) := by
  apply completionUnit_tensor_powerTorsion_isIso R a X _ n
  apply InducedCategory.hom_ext
  change a ^ n • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj N) = 0
  have h : a ^ n • 𝟙 N = 0 := by ext x; exact hN x
  have hs := congrArg (DerivedCategory.singleFunctor (ModuleCat R) 0).map h
  simpa only [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] using hs

end SerrePositivity.DerivedCompletion
