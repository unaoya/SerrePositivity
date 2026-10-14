module

public import SerrePositivity.KTheory.Adams.TensorCubeHighMixedKernel
public import SerrePositivity.KTheory.Adams.TensorCubeLowMixedExact
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
private lemma three_components_rotation {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasBinaryBiproducts C] {K U₀ U₁ U₂ : C} (τ : K ⟶ K)
    (m₀ : K ⟶ U₀) (m₁ : K ⟶ U₁) (m₂ : K ⟶ U₂)
    (r₀ : U₀ ⟶ U₁) (r₁ : U₁ ⟶ U₂) (r₂ : U₂ ⟶ U₀)
    (h₀ : τ ≫ m₀ = m₂ ≫ r₂) (h₁ : τ ≫ m₁ = m₀ ≫ r₀)
    (h₂ : τ ≫ m₂ = m₁ ≫ r₁) :
    τ ≫ biprod.lift m₀ (biprod.lift m₁ m₂) =
      biprod.lift m₀ (biprod.lift m₁ m₂) ≫
        biprod.lift (biprod.snd ≫ biprod.snd ≫ r₂)
          (biprod.lift (biprod.fst ≫ r₀) (biprod.snd ≫ biprod.fst ≫ r₁)) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd_assoc, h₀]
  · apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.lift_fst_assoc,
        biprod.lift_snd, h₁]
    · simp only [Category.assoc, biprod.lift_fst_assoc,
        biprod.lift_snd, biprod.lift_snd_assoc, h₂]

private lemma high_cokernel_iso_projection
    {C : Type*} [Category C] [Abelian C] (T : ShortComplex C) (hT : T.ShortExact) :
    cokernel.π T.f ≫ (shortExactCokernelIso T hT).hom = T.g :=
  (cokernelIsCokernel T.f).comp_coconePointUniqueUpToIso_hom
    hT.gIsCokernel WalkingParallelPair.one

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
  high_cokernel_iso_projection (tensorCubeHighMixedShortComplex S hS hproj)
    (tensorCubeHighMixedShortComplex_shortExact S hS hproj)

end Adams
end SerrePositivity
