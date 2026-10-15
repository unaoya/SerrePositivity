module
public import SerrePositivity.PerfectComplex.InvolutionClass
public import SerrePositivity.HomologicalAlgebra.CochainIdempotentAcyclic

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
  rw [k0Class,
    K0WithSupport.mk_eq_zero_of_acyclic Z
      (t.positive.image_strictlyPerfect hp) (t.positive.image_support hs)
      (t.positive.image_acyclic hac),
    K0WithSupport.mk_eq_zero_of_acyclic Z
      (t.negative.image_strictlyPerfect hp) (t.negative.image_support hs)
      (t.negative.image_acyclic hac), sub_self]

end CochainInvolution

end SerrePositivity
