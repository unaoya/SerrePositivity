import SerrePositivity.KTheory.SupportedCoefficients
import SerrePositivity.KTheory.Adams.Family
import SerrePositivity.PerfectComplex.CubicActionClass
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.K0WithSupport.Coefficients
assert_no_sorry SerrePositivity.K0WithSupport.coefficientEnlarge
assert_no_sorry SerrePositivity.K0WithSupport.coefficientCup
assert_no_sorry SerrePositivity.K0WithSupport.coefficientMap
assert_no_sorry SerrePositivity.K0WithSupport.coefficientCup_enlarge
assert_no_sorry SerrePositivity.K0WithSupport.coefficientCup_map
assert_no_sorry SerrePositivity.Adams.SupportedAdams.koszul
assert_no_sorry SerrePositivity.CochainCubicAction.weightedK0Class
#print axioms SerrePositivity.K0WithSupport.coefficientCup_map
#print axioms SerrePositivity.Adams.SupportedAdams.koszul
#print axioms SerrePositivity.CochainCubicAction.weightedK0Class

-- Basic operations retain arbitrary commutative coefficient and source rings.
open TensorProduct SerrePositivity
noncomputable section
example (E R : Type*) [CommRing E] [CommRing R]
    (Z W : TopologicalSpace.Closeds (PrimeSpectrum R)) (h : Z ≤ W) :
    K0WithSupport.Coefficients E Z →ₗ[E] K0WithSupport.Coefficients E W :=
  K0WithSupport.coefficientEnlarge E h
end
