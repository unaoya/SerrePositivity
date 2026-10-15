import SerrePositivity.KTheory.Adams.CyclicThreeFamily
import Mathlib.Util.AssertNoSorry

open CategoryTheory SerrePositivity
noncomputable section
universe u
example {R : Type u} [CommRing R] [Invertible (3 : R)]
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) (j : Fin 3) :
    τ.eigenK0Class t ht Z hp hs j =
      (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).k0Class Z hp hs := rfl

assert_no_sorry SerrePositivity.CochainCubicAction.eigenK0Class_eq_of_quasiIso
assert_no_sorry SerrePositivity.CochainCubicAction.weightedK0Class_eq_zero_of_acyclic
assert_no_sorry SerrePositivity.CochainCubicAction.eigenK0Class_shortExact
assert_no_sorry SerrePositivity.CochainCubicAction.weightedK0Class_shortExact
assert_no_sorry SerrePositivity.CochainCubicAction.weightedK0Class_tensor
assert_no_sorry SerrePositivity.Adams.cyclicThreeFamily
#print axioms SerrePositivity.CochainCubicAction.eigenK0Class_shortExact
#print axioms SerrePositivity.CochainCubicAction.weightedK0Class_tensor
#print axioms SerrePositivity.Adams.cyclicThreeFamily
