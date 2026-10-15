module

public import SerrePositivity.PerfectComplex.IdempotentImage
public import SerrePositivity.HomologicalAlgebra.CochainIdempotentHomology

/-! # Perfectness and support of idempotent images -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

namespace CochainIdempotent
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

lemma image_strictlyPerfect (e : CochainIdempotent K) (hK : strictlyPerfectComplex R K) :
    strictlyPerfectComplex R e.image := by
  obtain ⟨a, b, ha, hb⟩ := hK.1
  refine ⟨⟨a, b, ?_, ?_⟩, fun n => ?_⟩
  · exact (e.image.isStrictlyGE_iff a).mpr fun n hn =>
      e.image_isZero_X n (K.isZero_of_isStrictlyGE a n hn)
  · exact (e.image.isStrictlyLE_iff b).mpr fun n hn =>
      e.image_isZero_X n (K.isZero_of_isStrictlyLE b n hn)
  · have := (hK.2 n).1
    have := (hK.2 n).2
    exact ⟨e.image_finite_X n, e.image_projective_X n⟩

lemma image_support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (e : CochainIdempotent K) (hK : HasHomologySupportOn Z K) :
    HasHomologySupportOn Z e.image := by
  intro n
  exact (Module.support_subset_of_injective
    (HomologicalComplex.homologyMap e.inclusion n).hom
    (e.homology_inclusion_injective n)).trans (hK n)

end CochainIdempotent
end SerrePositivity
