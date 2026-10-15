module
public import SerrePositivity.PerfectComplex.InvolutionClass
public import SerrePositivity.PerfectComplex.TensorAcyclic

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
  have hb := (cochainAcyclic_iff_support_bot K).mp hac
  have hpos : t.positive.image.Acyclic :=
    (cochainAcyclic_iff_support_bot _).mpr (t.positive.image_support hb)
  have hneg : t.negative.image.Acyclic :=
    (cochainAcyclic_iff_support_bot _).mpr (t.negative.image_support hb)
  rw [k0Class,
    K0WithSupport.mk_eq_zero_of_acyclic Z
      (t.positive.image_strictlyPerfect hp) (t.positive.image_support hs) hpos,
    K0WithSupport.mk_eq_zero_of_acyclic Z
      (t.negative.image_strictlyPerfect hp) (t.negative.image_support hs) hneg, sub_self]

end CochainInvolution

end SerrePositivity
