import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTensor
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.derivedTensor_scalar_pow_zero_right
assert_no_sorry SerrePositivity.DerivedCompletion.derivedTensor_isComplete_of_right_scalar_pow_zero
assert_no_sorry SerrePositivity.DerivedCompletion.completionEquivalence_tensor_powerTorsion_isIso
assert_no_sorry SerrePositivity.DerivedCompletion.completionUnit_tensor_powerTorsion_isIso
assert_no_sorry SerrePositivity.DerivedCompletion.completionUnit_tensor_module_powerTorsion_isIso
#print axioms SerrePositivity.DerivedCompletion.derivedTensor_scalar_pow_zero_right
#print axioms SerrePositivity.DerivedCompletion.derivedTensor_isComplete_of_right_scalar_pow_zero
#print axioms SerrePositivity.DerivedCompletion.completionEquivalence_tensor_powerTorsion_isIso
#print axioms SerrePositivity.DerivedCompletion.completionUnit_tensor_powerTorsion_isIso
#print axioms SerrePositivity.DerivedCompletion.completionUnit_tensor_module_powerTorsion_isIso

noncomputable section
universe u
open CategoryTheory MonoidalCategory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

-- Check all degrees of the original unit, including exponent zero.
theorem audit_powerTorsion_tensor_unit_homology
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (N : ModuleCat.{u} R)
    (n : ℕ) (hN : ∀ x : N, a ^ n • x = 0) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map
      (((boundedAboveDerivedCompletionUnit R a).app X ▷
        boundedAboveDerivedSingleFunctor.obj N).hom)) := by
  have := completionUnit_tensor_module_powerTorsion_isIso R a X N n hN
  have : IsIso (DerivedCategory.Minus.ι.map
      ((boundedAboveDerivedCompletionUnit R a).app X ▷
        boundedAboveDerivedSingleFunctor.obj N)) := inferInstance
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map
    (DerivedCategory.Minus.ι.map
      ((boundedAboveDerivedCompletionUnit R a).app X ▷
        boundedAboveDerivedSingleFunctor.obj N)))
  infer_instance

-- The original base scalar is detected in both directions after completing the left factor.
theorem audit_powerTorsion_tensor_annihilator
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (N : ModuleCat.{u} R)
    (n : ℕ) (hN : ∀ x : N, a ^ n • x = 0) (i : ℤ) (s : R) :
    (∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      (X ⊗ boundedAboveDerivedSingleFunctor.obj N).obj, s • x = 0) ↔
    (∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((boundedAboveDerivedCompletionFunctor R a).obj X ⊗
        boundedAboveDerivedSingleFunctor.obj N).obj, s • x = 0) := by
  let f := (boundedAboveDerivedCompletionUnit R a).app X ▷
    boundedAboveDerivedSingleFunctor.obj N
  have : IsIso f := completionUnit_tensor_module_powerTorsion_isIso R a X N n hN
  let e := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
    (DerivedCategory.Minus.ι.mapIso (asIso f))
  constructor
  · intro h z
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective z
    rw [← e.toLinearEquiv.map_smul, h x, e.toLinearEquiv.map_zero]
  · intro h x
    apply e.toLinearEquiv.injective
    rw [e.toLinearEquiv.map_smul, h (e.toLinearEquiv x), e.toLinearEquiv.map_zero]

assert_no_sorry audit_powerTorsion_tensor_unit_homology
assert_no_sorry audit_powerTorsion_tensor_annihilator
#print axioms audit_powerTorsion_tensor_unit_homology
#print axioms audit_powerTorsion_tensor_annihilator
