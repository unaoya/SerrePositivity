module

public import SerrePositivity.KTheory.Adams.TensorSquareAdditivity
public import SerrePositivity.PerfectComplex.InvolutionClassAcyclic

/-! # Acyclic complexes have zero cyclic tensor-square class -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace Adams

lemma tensorSquareClass_eq_zero_of_acyclic
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) (hac : P.Acyclic) :
    tensorSquareClass P Z hp hs = 0 := by
  have ht : (tensorSquare P).Acyclic := (cochainAcyclic_iff_support_bot _).mpr
    (tensorSquare_support hp ((cochainAcyclic_iff_support_bot P).mp hac))
  exact (tensorSquareInvolution P).k0Class_eq_zero_of_acyclic Z
    (tensorSquare_perfect P hp) (tensorSquare_support hp hs) ht

end Adams
end SerrePositivity
