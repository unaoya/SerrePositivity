import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionTriangulated
import SerrePositivity.HomologicalAlgebra.DerivedModuleCone
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.completeProperty
assert_no_sorry SerrePositivity.DerivedCompletion.completeProperty_isClosedUnderIsomorphisms
assert_no_sorry SerrePositivity.DerivedCompletion.completeReflector
assert_no_sorry SerrePositivity.DerivedCompletion.completeProperty_isTriangulated
assert_no_sorry SerrePositivity.DerivedCompletion.completeReflectorAdjunction
assert_no_sorry SerrePositivity.DerivedCompletion.completeReflector_commShift
assert_no_sorry SerrePositivity.DerivedCompletion.completeReflectorAdjunction_commShift
assert_no_sorry SerrePositivity.DerivedCompletion.completeReflector_isTriangulated
assert_no_sorry SerrePositivity.DerivedCompletion.derivedComplexCompletionFunctor_commShift
assert_no_sorry SerrePositivity.DerivedCompletion.derivedComplexCompletionFunctor_isTriangulated
assert_no_sorry SerrePositivity.DerivedCompletion.completeReflectorAdjunction_unit
#print axioms SerrePositivity.DerivedCompletion.completeProperty
#print axioms SerrePositivity.DerivedCompletion.completeProperty_isClosedUnderIsomorphisms
#print axioms SerrePositivity.DerivedCompletion.completeProperty_isTriangulated
#print axioms SerrePositivity.DerivedCompletion.completeReflector
#print axioms SerrePositivity.DerivedCompletion.completeReflectorAdjunction
#print axioms SerrePositivity.DerivedCompletion.completeReflector_commShift
#print axioms SerrePositivity.DerivedCompletion.completeReflectorAdjunction_commShift
#print axioms SerrePositivity.DerivedCompletion.completeReflector_isTriangulated
#print axioms SerrePositivity.DerivedCompletion.derivedComplexCompletionFunctor_commShift
#print axioms SerrePositivity.DerivedCompletion.derivedComplexCompletionFunctor_isTriangulated
#print axioms SerrePositivity.DerivedCompletion.completeReflectorAdjunction_unit

noncomputable section
universe u
open CategoryTheory CategoryTheory.Pretriangulated SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

-- Apply the actual completion to the actual module-map cone triangle.
theorem audit_prop247_completed_module_triangle
    (R : Type u) [CommRing R] (a : R) (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (derivedComplexCompletionFunctor R a).mapTriangle.obj (moduleMapConeTriangle R f) ∈
      distTriang (ConcreteDerivedCategory R) :=
  (derivedComplexCompletionFunctor R a).map_distinguished _ (moduleMapConeTriangle_distinguished R f)

assert_no_sorry audit_prop247_completed_module_triangle
#print axioms audit_prop247_completed_module_triangle
