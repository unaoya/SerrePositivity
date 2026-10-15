import SerrePositivity.KTheory.MaximalSupportLength
import SerrePositivity.PerfectComplex.IntegerEuler
import Mathlib.Util.AssertNoSorry

open SerrePositivity IsLocalRing
universe u
example (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    K0WithSupport.integerEuler R =
      (maximalSupportLengthMap R).comp
        (K0WithSupport.homologyEuler (supportZeroLocus (maximalIdeal R))) := rfl

assert_no_sorry SerrePositivity.maximalSupportedModule_finiteLength
assert_no_sorry SerrePositivity.maximalSupportLengthMap
assert_no_sorry SerrePositivity.maximalSupportLengthMap_mk
assert_no_sorry SerrePositivity.K0WithSupport.integerEuler
assert_no_sorry SerrePositivity.K0WithSupport.integerEuler_mk_complex_real
#print axioms SerrePositivity.maximalSupportLengthMap
