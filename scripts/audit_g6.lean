import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Jacobson
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.isUnit_one_sub_mul_of_recurrence_bijective
assert_no_sorry SerrePositivity.DerivedCompletion.mem_jacobson_bot_of_isModuleComplete
assert_no_sorry SerrePositivity.DerivedCompletion.isUnit_one_sub_mul_of_isModuleComplete
#print axioms SerrePositivity.DerivedCompletion.mem_jacobson_bot_of_isModuleComplete
#print axioms SerrePositivity.DerivedCompletion.isUnit_one_sub_mul_of_isModuleComplete

example (T : Type*) [CommRing T] (a : T)
    (h : SerrePositivity.DerivedCompletion.IsModuleComplete T a (ModuleCat.of T T)) :
    a ∈ Ideal.jacobson (⊥ : Ideal T) :=
  SerrePositivity.DerivedCompletion.mem_jacobson_bot_of_isModuleComplete T a h
