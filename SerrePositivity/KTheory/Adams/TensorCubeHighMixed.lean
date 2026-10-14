module

public import SerrePositivity.KTheory.Adams.TensorCubeFirstLayer

/-! # The first high mixed component of the tensor-cube filtration -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

/-- Extract two quotient factors and lift the remaining factor into A. -/
def tensorCubeHighMixed0 : tensorCubeKernel S.g ⟶
    cochainTensor (cochainTensor S.X₃ S.X₃) S.X₁ := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  have hT := cochainTensorTripleShortComplexThird_shortExact S.X₃ S.X₃ S σ
  have := hT.mono_f
  exact hT.exact.lift (tensorCubeKernelInclusion S.g ≫ tensorCubePairMap0 S.g) (by
    change (tensorCubeKernelInclusion S.g ≫ tensorCubePairMap0 S.g) ≫
      cochainTensorMap (𝟙 (cochainTensor S.X₃ S.X₃)) S.g = 0
    simp only [tensorCubePairMap0, cochainTensorTripleMap, Category.assoc,
      cochainTensorMap_comp, comp_id, id_comp]
    exact kernel.condition (tensorCubeMap S.g))

@[reassoc]
lemma tensorCubeHighMixed0_inclusion :
    tensorCubeHighMixed0 S hS hproj ≫ cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₃) S.f =
      tensorCubeKernelInclusion S.g ≫ tensorCubePairMap0 S.g := by
  rw [cochainTensorTripleMap, cochainTensorMap_id]
  dsimp [tensorCubeHighMixed0]
  exact Fork.IsLimit.lift_ι _

include hS hproj in
lemma tensorCubeHighMixed0_target_inclusion_mono :
    Mono (cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₃) S.f) := by
  rw [cochainTensorTripleMap, cochainTensorMap_id]
  exact (cochainTensorTripleShortComplexThird_shortExact S.X₃ S.X₃ S
    (cochainDegreewiseSplittingOfProjective S hS hproj)).mono_f

@[simp, reassoc]
lemma tensorCubeFirstLayerToKernel_highMixed0 :
    tensorCubeFirstLayerToKernel S.g ≫ tensorCubeHighMixed0 S hS hproj = 0 := by
  have := tensorCubeHighMixed0_target_inclusion_mono S hS hproj
  apply (cancel_mono (cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₃) S.f)).mp
  rw [Category.assoc, tensorCubeHighMixed0_inclusion,
    tensorCubeFirstLayerToKernel_inclusion_assoc, tensorCubeFirstLayerInclusion_pair0]
  simp only [zero_comp]

end Adams
end SerrePositivity
