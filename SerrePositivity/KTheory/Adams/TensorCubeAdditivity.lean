module

public import SerrePositivity.KTheory.Adams.TensorCubeMixedCancellation
public import SerrePositivity.PerfectComplex.CubicActionShortExact

/-! # Additivity of the weighted cyclic tensor-cube class -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
open CategoryTheory Category Limits
namespace Adams
variable {R : Type u} [CommRing R] [Invertible (3 : R)]

/-- The cubic eigenspace classes weighted by a root in the coefficient ring. -/
def tensorCubeClass (E : Type v) [CommRing E] (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    K0WithSupport.Coefficients E Z :=
  (tensorCubeAction P).weightedK0Class E t ht ζ Z
    (tensorCube_perfect P hp) (tensorCube_support hp hs)

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1200000 in
-- The three filtered sequences cumulatively normalize tensor, kernel and biproduct models.
lemma tensorCubeClass_shortExact (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (ha : strictlyPerfectComplex R S.X₁) (hp : strictlyPerfectComplex R S.X₂)
    (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsP : HasHomologySupportOn Z S.X₂)
    (hsD : HasHomologySupportOn Z S.X₃) :
    tensorCubeClass E t ht ζ S.X₂ Z hp hsP =
      tensorCubeClass E t ht ζ S.X₁ Z ha hsA + tensorCubeClass E t ht ζ S.X₃ Z hd hsD := by
  let hproj := fun i => (hd.2 i).2
  have hout := CochainCubicAction.weightedK0Class_shortExact
    (tensorCubeKernelShortComplex S.g) (tensorCubeKernelAction S.g)
    (tensorCubeAction S.X₂) (tensorCubeAction S.X₃)
    (tensorCubeKernelRotation_inclusion S.g) (tensorCubeRotation_naturality S.g).symm t ht
    E ζ Z (tensorCubeKernelShortComplex_shortExact S hS hproj)
    (tensorCubeKernel_perfect S hS hp hd) (tensorCube_perfect S.X₂ hp)
    (tensorCube_perfect S.X₃ hd) (tensorCubeKernel_support S hS hp hd hsP hsD)
    (tensorCube_support hp hsP) (tensorCube_support hd hsD)
  have hhigh := CochainCubicAction.weightedK0Class_shortExact
    (tensorCubeHighMixedShortComplex S hS hproj) (tensorCubeFirstLayerAction S.g)
    (tensorCubeKernelAction S.g) (tensorCubeHighMixedAction S)
    (by
      dsimp only [tensorCubeHighMixedShortComplex, tensorCubeFirstLayerAction,
        tensorCubeKernelAction]
      exact (tensorCubeFirstLayerToKernel_rotation S.g).symm)
    (by
      dsimp only [tensorCubeHighMixedShortComplex, tensorCubeKernelAction,
        tensorCubeHighMixedAction, cochainTensorCyclicSumAction]
      exact tensorCubeHighMixedMap_rotation S hS hproj) t ht E ζ Z
    (tensorCubeHighMixedShortComplex_shortExact S hS hproj)
    (tensorCubeFirstLayer_perfect S hS hp hd) (tensorCubeKernel_perfect S hS hp hd)
    (tensorCubeHighMixedTarget_perfect S ha hd) (tensorCubeFirstLayer_support S hS ha hd hsA hsD)
    (tensorCubeKernel_support S hS hp hd hsP hsD)
    (tensorCubeHighMixedTarget_support S ha hd hsA hsD)
  have hlow := CochainCubicAction.weightedK0Class_shortExact
    (tensorCubeLowMixedShortComplex S hS hproj) (tensorCubeAction S.X₁)
    (tensorCubeFirstLayerAction S.g) (tensorCubeLowMixedAction S)
    (by
      dsimp only [tensorCubeLowMixedShortComplex, tensorCubeAction, tensorCubeFirstLayerAction]
      exact (tensorCubeFirstLayerFirstMap_rotation S).symm)
    (by
      dsimp only [tensorCubeLowMixedShortComplex, tensorCubeFirstLayerAction,
        tensorCubeLowMixedAction, cochainTensorCyclicSumAction]
      exact tensorCubeLowMixedMap_rotation S hS hproj)
    t ht E ζ Z (tensorCubeLowMixedShortComplex_shortExact S hS hproj)
    (tensorCube_perfect S.X₁ ha) (tensorCubeFirstLayer_perfect S hS hp hd)
    (tensorCubeLowMixedTarget_perfect S ha hd) (tensorCube_support ha hsA)
    (tensorCubeFirstLayer_support S hS ha hd hsA hsD)
    (tensorCubeLowMixedTarget_support S ha hd hsA hsD)
  dsimp only [tensorCubeKernelShortComplex, tensorCubeHighMixedShortComplex,
    tensorCubeLowMixedShortComplex] at hout hhigh hlow
  dsimp only [tensorCubeClass]
  rw [hout, hhigh, hlow,
    tensorCubeLowMixed_weightedK0Class_eq_zero E S t ht ζ Z ha hd hsA hsD hζ,
    tensorCubeHighMixed_weightedK0Class_eq_zero E S t ht ζ Z ha hd hsA hsD hζ,
    add_zero, add_zero]

end Adams
end SerrePositivity
