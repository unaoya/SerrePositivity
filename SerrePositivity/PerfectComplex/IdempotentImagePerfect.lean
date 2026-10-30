module

public import SerrePositivity.PerfectComplex.ClosedSupportRelations
public import SerrePositivity.HomologicalAlgebra.CochainIdempotent
public import SerrePositivity.PerfectComplex.DegreewiseRetract
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
    strictlyPerfectComplex R e.image :=
  strictlyPerfectComplex_of_degreewiseRetract e.inclusion e.projection.f
    (fun n => congrArg (fun f => f.f n) e.inclusion_projection) hK

lemma image_support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (e : CochainIdempotent K) (hK : HasHomologySupportOn Z K) :
    HasHomologySupportOn Z e.image := by
  intro n
  exact (Module.support_subset_of_injective
    (HomologicalComplex.homologyMap e.inclusion n).hom
    (e.homology_inclusion_injective n)).trans (hK n)

end CochainIdempotent
end SerrePositivity
