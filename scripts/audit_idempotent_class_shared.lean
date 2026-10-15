import SerrePositivity.PerfectComplex.IdempotentImageClass
import Mathlib.Util.AssertNoSorry

open CategoryTheory SerrePositivity
noncomputable section
universe u

-- No inverse for 2 or 3, locality, or regularity is required by the common class.
example {R : Type u} [CommRing R] {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : CochainIdempotent K) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) :
    e.k0Class Z hp hs = K0WithSupport.mk Z (supportedPerfectOnObj Z e.image
      (e.image_strictlyPerfect hp) (e.image_support hs)) := rfl

assert_no_sorry SerrePositivity.CochainIdempotent.k0Class
assert_no_sorry SerrePositivity.CochainIdempotent.k0Class_eq_of_quasiIso
assert_no_sorry SerrePositivity.CochainIdempotent.k0Class_eq_zero_of_acyclic
assert_no_sorry SerrePositivity.CochainIdempotent.k0Class_shortExact
#print axioms SerrePositivity.CochainIdempotent.k0Class_eq_of_quasiIso
#print axioms SerrePositivity.CochainIdempotent.k0Class_eq_zero_of_acyclic
#print axioms SerrePositivity.CochainIdempotent.k0Class_shortExact
