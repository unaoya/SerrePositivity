import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FiniteTensorComplete
import SerrePositivity.CommutativeAlgebra.PerfectoidDerivedComplete
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.scalarComplexTowerDifference_isIso_of_terms
assert_no_sorry SerrePositivity.DerivedCompletion.isComplete_Q_of_terms
assert_no_sorry SerrePositivity.DerivedCompletion.isModuleComplete_tensor_finite_free
assert_no_sorry SerrePositivity.DerivedCompletion.isComplete_Q_extend_chain_of_terms
assert_no_sorry SerrePositivity.DerivedCompletion.realizedDerivedTensor_isComplete_of_finite_free_resolution
assert_no_sorry SerrePositivity.DerivedCompletion.boundedAboveDerivedTensor_isComplete_of_finite_regular
assert_no_sorry SerrePositivity.IsIntegralPerfectoid.isModuleComplete
assert_no_sorry SerrePositivity.IsIntegralPerfectoid.isModuleComplete_algebra
#print axioms SerrePositivity.DerivedCompletion.scalarComplexTowerDifference_isIso_of_terms
#print axioms SerrePositivity.DerivedCompletion.isComplete_Q_of_terms
#print axioms SerrePositivity.DerivedCompletion.isModuleComplete_tensor_finite_free
#print axioms SerrePositivity.DerivedCompletion.isComplete_Q_extend_chain_of_terms
#print axioms SerrePositivity.DerivedCompletion.realizedDerivedTensor_isComplete_of_finite_free_resolution
#print axioms SerrePositivity.DerivedCompletion.boundedAboveDerivedTensor_isComplete_of_finite_regular
#print axioms SerrePositivity.IsIntegralPerfectoid.isModuleComplete
#print axioms SerrePositivity.IsIntegralPerfectoid.isModuleComplete_algebra

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

-- No upper or lower bound is imposed on the cochain complex.
example (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i, IsModuleComplete R a (K.X i)) :
    IsComplete R a (DerivedCategory.Q.obj K) := isComplete_Q_of_terms R a K hK

-- Rank zero is included without a nontriviality assumption on the ring.
example (M : ModuleCat.{u} R) (hM : IsModuleComplete R a M) :
    IsModuleComplete R a ((tensorLeft M).obj (ModuleCat.of R (Fin 0 → R))) :=
  isModuleComplete_tensor_finite_free R a M _ hM

-- Actual finite test modules are not required to be complete or p-regular.
example [IsRegularLocalRing R] (M N : ModuleCat.{u} R) [Module.Finite R N]
    (hM : IsModuleComplete R a M) :
    IsComplete R a ((boundedAboveDerivedTensorModuleFunctor M).obj N) :=
  boundedAboveDerivedTensor_isComplete_of_finite_regular R a M N hM
