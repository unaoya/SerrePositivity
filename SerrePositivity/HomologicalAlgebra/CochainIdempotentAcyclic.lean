module
public import SerrePositivity.HomologicalAlgebra.CochainIdempotentHomology

/-! # Idempotent images preserve acyclicity -/
@[expose] public section
universe u
namespace SerrePositivity.CochainIdempotent
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R] {K : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Homology of an idempotent image is a retract of the original homology. -/
lemma image_acyclic (e : CochainIdempotent K) (hK : K.Acyclic) : e.image.Acyclic := by
  intro n
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ n).mpr
  rw [IsZero.iff_id_eq_zero, ← e.homology_inclusion_projection n]
  rw [(hK n).isZero_homology.eq_of_tgt (homologyMap e.inclusion n) 0, zero_comp]

end SerrePositivity.CochainIdempotent
