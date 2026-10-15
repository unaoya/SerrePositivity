module

public import SerrePositivity.PerfectComplex.IdempotentDecomposition
public import SerrePositivity.PerfectComplex.TensorSupport
public import SerrePositivity.HomologicalAlgebra.CochainIdempotentTensor

/-! # Tensor products of idempotent images -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]
namespace CochainIdempotent
variable {P Q : CochainComplex (ModuleCat.{u} R) ℤ}

lemma tensor_image_perfect (e : CochainIdempotent P) (d : CochainIdempotent Q)
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    strictlyPerfectComplex R (tensor e d).image :=
  (tensor e d).image_strictlyPerfect (strictlyPerfectComplex_cochainTensor P Q hp hq)

lemma tensor_image_support (e : CochainIdempotent P) (d : CochainIdempotent Q)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Y P) (hsQ : HasHomologySupportOn Z Q) :
    HasHomologySupportOn (Y ⊓ Z) (tensor e d).image :=
  (tensor e d).image_support (hsP.cochainTensor hsQ hp hq)

end CochainIdempotent
end SerrePositivity
