module
public import SerrePositivity.CategoryTheory.Triangulated.Idempotent

public import SerrePositivity.KTheory.Adams.TensorCubeHighMixedKernel
public import SerrePositivity.CategoryTheory.Abelian.ShortComplex
public import SerrePositivity.PerfectComplex.TensorTripleCyclicSumPerfect

/-! # The high mixed quotient, with support and cubic action -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))

lemma tensorCubeHighMixedTarget_perfect
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃) :
    strictlyPerfectComplex R (tensorCubeHighMixedTarget S) :=
  cochainTensorCyclicSum_perfect _ _ _ hd hd ha

lemma tensorCubeHighMixedTarget_support
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (ha : strictlyPerfectComplex R S.X₁) (hd : strictlyPerfectComplex R S.X₃)
    (hsA : HasHomologySupportOn Z S.X₁) (hsD : HasHomologySupportOn Z S.X₃) :
    HasHomologySupportOn Z (tensorCubeHighMixedTarget S) :=
  cochainTensorCyclicSum_support _ _ _ hd hd ha hsD hsD hsA

abbrev tensorCubeHighMixedRotation : tensorCubeHighMixedTarget S ⟶ tensorCubeHighMixedTarget S :=
  cochainTensorCyclicSumRotation S.X₃ S.X₃ S.X₁

lemma tensorCubeHighMixedRotation_cube :
    tensorCubeHighMixedRotation S ≫ tensorCubeHighMixedRotation S ≫
      tensorCubeHighMixedRotation S = 𝟙 _ :=
  cochainTensorCyclicSumRotation_cube S.X₃ S.X₃ S.X₁

abbrev tensorCubeHighMixedAction : CochainCubicAction (tensorCubeHighMixedTarget S) :=
  cochainTensorCyclicSumAction S.X₃ S.X₃ S.X₁

variable (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

set_option maxHeartbeats 600000 in
-- Compare the combined tensor maps with the nested biproduct rotation.
lemma tensorCubeHighMixedMap_rotation :
    tensorCubeKernelRotation S.g ≫ tensorCubeHighMixedMap S hS hproj =
      tensorCubeHighMixedMap S hS hproj ≫ tensorCubeHighMixedRotation S :=
  three_components_rotation (tensorCubeKernelRotation S.g)
    (tensorCubeHighMixed0 S hS hproj) (tensorCubeHighMixed1 S hS hproj)
    (tensorCubeHighMixed2 S hS hproj) (cochainTensorRotationIso S.X₃ S.X₃ S.X₁).hom
    (cochainTensorRotationIso S.X₁ S.X₃ S.X₃).hom
    (cochainTensorRotationIso S.X₃ S.X₁ S.X₃).hom
    (tensorCubeKernelRotation_highMixed0 S hS hproj)
    (tensorCubeKernelRotation_highMixed1 S hS hproj)
    (tensorCubeKernelRotation_highMixed2 S hS hproj)

/-- The chosen cokernel model of the high mixed short complex. -/
abbrev tensorCubeHighMixedCokernel :=
  cokernel (tensorCubeHighMixedShortComplex S hS hproj).f

/-- The quotient of F₂ by F₁ is the high mixed cyclic sum. -/
def tensorCubeHighMixedCokernelIso :=
  shortExactCokernelIso (tensorCubeHighMixedShortComplex S hS hproj)
    (tensorCubeHighMixedShortComplex_shortExact S hS hproj)

lemma tensorCubeHighMixedCokernelIso_π_hom :
    cokernel.π (tensorCubeHighMixedShortComplex S hS hproj).f ≫
      (tensorCubeHighMixedCokernelIso S hS hproj).hom =
        (tensorCubeHighMixedShortComplex S hS hproj).g :=
  shortExactCokernelIso_π_hom (tensorCubeHighMixedShortComplex S hS hproj)
    (tensorCubeHighMixedShortComplex_shortExact S hS hproj)

end Adams
end SerrePositivity
