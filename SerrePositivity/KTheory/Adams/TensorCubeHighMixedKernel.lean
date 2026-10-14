module

public import SerrePositivity.KTheory.Adams.TensorCubeHighMixedEpi

/-! # Identification of the kernel of the high mixed quotient -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

@[simp, reassoc]
lemma tensorCubeFirstLayerToKernel_highMixed1 :
    tensorCubeFirstLayerToKernel S.g ≫ tensorCubeHighMixed1 S hS hproj = 0 := by
  have := tensorCubeHighMixed1_target_inclusion_mono S hS hproj
  apply (cancel_mono (cochainTensorTripleMap S.f (𝟙 S.X₃) (𝟙 S.X₃))).mp
  rw [Category.assoc, tensorCubeHighMixed1_inclusion,
    tensorCubeFirstLayerToKernel_inclusion_assoc, tensorCubeFirstLayerInclusion_pair1]
  simp only [zero_comp]

@[simp, reassoc]
lemma tensorCubeFirstLayerToKernel_highMixed2 :
    tensorCubeFirstLayerToKernel S.g ≫ tensorCubeHighMixed2 S hS hproj = 0 := by
  have := tensorCubeHighMixed2_target_inclusion_mono S hS hproj
  apply (cancel_mono (cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₃))).mp
  rw [Category.assoc, tensorCubeHighMixed2_inclusion,
    tensorCubeFirstLayerToKernel_inclusion_assoc, tensorCubeFirstLayerInclusion_pair2]
  simp only [zero_comp]

@[simp]
lemma tensorCubeFirstLayerToKernel_highMixedMap :
    tensorCubeFirstLayerToKernel S.g ≫ tensorCubeHighMixedMap S hS hproj = 0 := by
  apply biprod.hom_ext
  · simp only [tensorCubeHighMixedMap, Category.assoc, biprod.lift_fst,
      tensorCubeFirstLayerToKernel_highMixed0, zero_comp]
  · apply biprod.hom_ext
    · simp only [tensorCubeHighMixedMap, Category.assoc, biprod.lift_snd_assoc,
        biprod.lift_fst, tensorCubeFirstLayerToKernel_highMixed1, zero_comp]
    · simp only [tensorCubeHighMixedMap, Category.assoc,
        biprod.lift_snd, tensorCubeFirstLayerToKernel_highMixed2, zero_comp]

lemma tensorCubeHighMixedMap_kernel_pair_zero
    {W : CochainComplex (ModuleCat.{u} R) ℤ} (v : W ⟶ tensorCubeKernel S.g)
    (hv : v ≫ tensorCubeHighMixedMap S hS hproj = 0) :
    (v ≫ tensorCubeKernelInclusion S.g) ≫ tensorCubePairMap S.g = 0 := by
  have h₀ : v ≫ tensorCubeHighMixed0 S hS hproj = 0 := by
    simpa only [tensorCubeHighMixedMap, Category.assoc, biprod.lift_fst, zero_comp] using
      hv =≫ biprod.fst
  have h₁ : v ≫ tensorCubeHighMixed1 S hS hproj = 0 := by
    simpa only [tensorCubeHighMixedMap, Category.assoc, biprod.lift_snd_assoc,
      biprod.lift_fst, zero_comp] using hv =≫ (biprod.snd ≫ biprod.fst)
  have h₂ : v ≫ tensorCubeHighMixed2 S hS hproj = 0 := by
    simpa only [tensorCubeHighMixedMap, Category.assoc, biprod.lift_snd_assoc,
      biprod.lift_snd, zero_comp] using hv =≫ (biprod.snd ≫ biprod.snd)
  apply biprod.hom_ext
  · simp only [tensorCubePairMap, Category.assoc, biprod.lift_fst, zero_comp]
    rw [← tensorCubeHighMixed0_inclusion S hS hproj, ← Category.assoc, h₀, zero_comp]
  · apply biprod.hom_ext
    · simp only [tensorCubePairMap, Category.assoc, biprod.lift_snd_assoc,
        biprod.lift_fst, zero_comp]
      rw [← tensorCubeHighMixed1_inclusion S hS hproj, ← Category.assoc, h₁, zero_comp]
    · simp only [tensorCubePairMap, Category.assoc,
        biprod.lift_snd, zero_comp]
      rw [← tensorCubeHighMixed2_inclusion S hS hproj, ← Category.assoc, h₂, zero_comp]

/-- A morphism killed by the high mixed quotient factors through the first layer. -/
def tensorCubeHighMixedKernelLift
    {W : CochainComplex (ModuleCat.{u} R) ℤ} (v : W ⟶ tensorCubeKernel S.g)
    (hv : v ≫ tensorCubeHighMixedMap S hS hproj = 0) : W ⟶ tensorCubeFirstLayer S.g :=
  kernel.lift (tensorCubePairMap S.g) (v ≫ tensorCubeKernelInclusion S.g)
    (tensorCubeHighMixedMap_kernel_pair_zero S hS hproj v hv)

lemma tensorCubeHighMixedKernelLift_fac
    {W : CochainComplex (ModuleCat.{u} R) ℤ} (v : W ⟶ tensorCubeKernel S.g)
    (hv : v ≫ tensorCubeHighMixedMap S hS hproj = 0) :
    tensorCubeHighMixedKernelLift S hS hproj v hv ≫ tensorCubeFirstLayerToKernel S.g = v := by
  apply (cancel_mono (tensorCubeKernelInclusion S.g)).mp
  rw [Category.assoc, tensorCubeFirstLayerToKernel_inclusion,
    tensorCubeHighMixedKernelLift, kernel.lift_ι]

abbrev tensorCubeHighMixedShortComplex :=
  ShortComplex.mk (tensorCubeFirstLayerToKernel S.g) (tensorCubeHighMixedMap S hS hproj)
    (tensorCubeFirstLayerToKernel_highMixedMap S hS hproj)

set_option maxHeartbeats 600000 in
-- Compare the kernel-fork model with the first-layer inclusion into the outer kernel.
/-- The first layer is the kernel of the high mixed quotient. -/
def tensorCubeHighMixedIsKernel :
    IsLimit (KernelFork.ofι (tensorCubeFirstLayerToKernel S.g)
      (tensorCubeFirstLayerToKernel_highMixedMap S hS hproj)) :=
  KernelFork.IsLimit.ofι' (tensorCubeFirstLayerToKernel S.g)
    (tensorCubeFirstLayerToKernel_highMixedMap S hS hproj) (fun v hv =>
    ⟨tensorCubeHighMixedKernelLift S hS hproj v hv,
      tensorCubeHighMixedKernelLift_fac S hS hproj v hv⟩)

set_option maxHeartbeats 600000 in
-- Identify the kernel fork with the short-complex fields when transferring exactness.
lemma tensorCubeHighMixedShortComplex_shortExact :
    (tensorCubeHighMixedShortComplex S hS hproj).ShortExact := by
  have := tensorCubeHighMixedMap_epi S hS hproj
  refine { exact := ?_ }
  exact ShortComplex.exact_of_f_is_kernel
    (tensorCubeHighMixedShortComplex S hS hproj) (tensorCubeHighMixedIsKernel S hS hproj)

end Adams
end SerrePositivity
