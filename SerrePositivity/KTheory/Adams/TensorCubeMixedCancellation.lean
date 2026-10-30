module

public import SerrePositivity.PerfectComplex.CubicActionTransport
public import SerrePositivity.KTheory.Adams.TensorCubeLowMixedSupport
public import SerrePositivity.KTheory.Adams.TensorCubeLowMixedRotation
public import SerrePositivity.KTheory.Adams.TensorCubeHighMixedQuotient
public import SerrePositivity.PerfectComplex.TensorTripleCyclicSumClass

/-! # Cancellation of both mixed layers of the tensor-cube filtration -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
open CategoryTheory
namespace Adams
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
variable (E : Type v) [CommRing E]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
variable (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

lemma tensorCubeLowMixed_weightedK0Class_eq_zero
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsD : HasHomologySupportOn Z S.X₃)
    (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (tensorCubeLowMixedAction S).weightedK0Class E t ht ζ Z
      (tensorCubeLowMixedTarget_perfect S ha hd)
      (tensorCubeLowMixedTarget_support S ha hd hsA hsD) = 0 :=
  cochainTensorCyclicSum_weightedK0Class_eq_zero S.X₃ S.X₁ S.X₁ t ht Z
    hd ha ha hsD hsA hsA E ζ hζ

lemma tensorCubeHighMixed_weightedK0Class_eq_zero
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsD : HasHomologySupportOn Z S.X₃)
    (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (tensorCubeHighMixedAction S).weightedK0Class E t ht ζ Z
      (tensorCubeHighMixedTarget_perfect S ha hd)
      (tensorCubeHighMixedTarget_support S ha hd hsA hsD) = 0 :=
  cochainTensorCyclicSum_weightedK0Class_eq_zero S.X₃ S.X₃ S.X₁ t ht Z
    hd hd ha hsD hsD hsA E ζ hζ

end Adams
end SerrePositivity
