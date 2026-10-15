module

public import SerrePositivity.PerfectComplex.InvolutionAntiEquivariance
public import SerrePositivity.PerfectComplex.IdempotentImageClass

/-! # The difference of involution eigenspace classes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace CochainInvolution
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

def k0Class (t : CochainInvolution K) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) : K0WithSupport Z :=
  t.positive.k0Class Z hp hs - t.negative.k0Class Z hp hs

lemma k0Class_eq_zero_of_anticommute (t : CochainInvolution K)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K)
    (a : K ⟶ K) (ha : t.map ≫ a = -(a ≫ t.map)) (haa : a ≫ a = 𝟙 K) :
    t.k0Class Z hp hs = 0 := by
  apply sub_eq_zero.mpr
  let e := t.positiveNegativeIso a ha haa
  exact K0WithSupport.mk_eq_of_quasiIso Z t.positive.image t.negative.image
    (t.positive.image_strictlyPerfect hp) (t.negative.image_strictlyPerfect hp)
    (t.positive.image_support hs) (t.negative.image_support hs) e.hom

end CochainInvolution
end SerrePositivity
