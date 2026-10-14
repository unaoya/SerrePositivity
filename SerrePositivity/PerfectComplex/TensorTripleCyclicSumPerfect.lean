module

public import SerrePositivity.PerfectComplex.TensorTripleCyclicSum
public import SerrePositivity.PerfectComplex.BiproductPerfect
public import SerrePositivity.PerfectComplex.TensorSupport

/-! # Perfectness and support of the three cyclic tensor summands -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R]
variable (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)

lemma cochainTensorCyclicSum_perfect
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (ht : strictlyPerfectComplex R T) :
    strictlyPerfectComplex R (cochainTensorCyclicSum P Q T) :=
  strictlyPerfectComplex_biprod
    (strictlyPerfectComplex_cochainTensor _ _ (strictlyPerfectComplex_cochainTensor _ _ hp hq) ht)
    (strictlyPerfectComplex_biprod
      (strictlyPerfectComplex_cochainTensor _ _ (strictlyPerfectComplex_cochainTensor _ _ ht hp) hq)
      (strictlyPerfectComplex_cochainTensor _ _
        (strictlyPerfectComplex_cochainTensor _ _ hq ht) hp))

lemma cochainTensorCyclicSum_support
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (ht : strictlyPerfectComplex R T)
    (hsP : HasHomologySupportOn Z P) (hsQ : HasHomologySupportOn Z Q)
    (hsT : HasHomologySupportOn Z T) : HasHomologySupportOn Z (cochainTensorCyclicSum P Q T) :=
  ((hsP.cochainTensor_left hp Q).cochainTensor_left
    (strictlyPerfectComplex_cochainTensor _ _ hp hq) T).biprod
    (((hsT.cochainTensor_left ht P).cochainTensor_left
      (strictlyPerfectComplex_cochainTensor _ _ ht hp) Q).biprod
      ((hsQ.cochainTensor_left hq T).cochainTensor_left
        (strictlyPerfectComplex_cochainTensor _ _ hq ht) P))

end SerrePositivity
