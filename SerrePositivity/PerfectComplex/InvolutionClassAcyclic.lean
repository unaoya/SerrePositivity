module
public import SerrePositivity.PerfectComplex.InvolutionClass

/-! # The class of an involution on an acyclic perfect complex vanishes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace CochainInvolution

lemma k0Class_eq_zero_of_acyclic {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (t : CochainInvolution K) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) (hac : K.Acyclic) :
    t.k0Class Z hp hs = 0 := by
  rw [k0Class, t.positive.k0Class_eq_zero_of_acyclic Z hp hs hac,
    t.negative.k0Class_eq_zero_of_acyclic Z hp hs hac, sub_self]

end CochainInvolution

end SerrePositivity
