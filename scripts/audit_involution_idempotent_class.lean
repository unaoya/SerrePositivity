import SerrePositivity.KTheory.Adams.CyclicTwoFamily
import Mathlib.Util.AssertNoSorry

open CategoryTheory SerrePositivity
noncomputable section
universe u
variable {R : Type u} [CommRing R] [Invertible (2 : R)]
variable {K : CochainComplex (ModuleCat.{u} R) ℤ} (t : CochainInvolution K)
variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
variable (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K)

example : t.k0Class Z hp hs = t.positive.k0Class Z hp hs - t.negative.k0Class Z hp hs := rfl
example : t.positiveClass Z hp hs = t.positive.k0Class Z hp hs := rfl
example : t.negativeClass Z hp hs = t.negative.k0Class Z hp hs := rfl

assert_no_sorry SerrePositivity.CochainInvolution.k0Class_shortExact
assert_no_sorry SerrePositivity.CochainInvolution.k0Class_eq_zero_of_acyclic
assert_no_sorry SerrePositivity.CochainInvolution.k0Class_tensor
assert_no_sorry SerrePositivity.Adams.cyclicTwoFamily
#print axioms SerrePositivity.CochainInvolution.k0Class_shortExact
#print axioms SerrePositivity.CochainInvolution.k0Class_tensor
#print axioms SerrePositivity.Adams.cyclicTwoFamily
