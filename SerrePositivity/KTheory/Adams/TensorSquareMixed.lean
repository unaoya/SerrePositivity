module

public import SerrePositivity.KTheory.Adams.TensorSquareFiltration

/-! # Canonical mixed-component maps of the tensor-square filtration -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]

namespace Adams
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
  (hproj : ∀ i, Module.Projective R (S.X₃.X i))

/-- Extract the `A ⊗ D` component by the universal property of the tensor kernel. -/
def tensorSquareMixedLeft : tensorSquareKernel S.g ⟶ cochainTensor S.X₁ S.X₃ := by
  have hT := cochainTensorShortComplexRight_shortExact_of_projective S hS hproj S.X₃
  have := hT.mono_f
  exact hT.exact.lift
    (tensorSquareKernelInclusion S.g ≫ cochainTensorMap (𝟙 S.X₂) S.g) (by
      change (tensorSquareKernelInclusion S.g ≫ cochainTensorMap (𝟙 S.X₂) S.g) ≫
        cochainTensorMap S.g (𝟙 S.X₃) = 0
      rw [Category.assoc, cochainTensorMap_comp, id_comp, comp_id, kernel.condition])

@[reassoc]
lemma tensorSquareMixedLeft_inclusion :
    tensorSquareMixedLeft S hS hproj ≫ cochainTensorMap S.f (𝟙 S.X₃) =
      tensorSquareKernelInclusion S.g ≫ cochainTensorMap (𝟙 S.X₂) S.g := by
  dsimp [tensorSquareMixedLeft]
  exact Fork.IsLimit.lift_ι _

/-- Extract the `D ⊗ A` component by the universal property of the other tensor kernel. -/
def tensorSquareMixedRight : tensorSquareKernel S.g ⟶ cochainTensor S.X₃ S.X₁ := by
  have hT := cochainTensorShortComplexLeft_shortExact_of_projective S.X₃ S hS hproj
  have := hT.mono_f
  exact hT.exact.lift
    (tensorSquareKernelInclusion S.g ≫ cochainTensorMap S.g (𝟙 S.X₂)) (by
      change (tensorSquareKernelInclusion S.g ≫ cochainTensorMap S.g (𝟙 S.X₂)) ≫
        cochainTensorMap (𝟙 S.X₃) S.g = 0
      rw [Category.assoc, cochainTensorMap_comp, comp_id, id_comp, kernel.condition])

@[reassoc]
lemma tensorSquareMixedRight_inclusion :
    tensorSquareMixedRight S hS hproj ≫ cochainTensorMap (𝟙 S.X₃) S.f =
      tensorSquareKernelInclusion S.g ≫ cochainTensorMap S.g (𝟙 S.X₂) := by
  dsimp [tensorSquareMixedRight]
  exact Fork.IsLimit.lift_ι _

@[simp]
lemma tensorSquareKernelFirstMap_mixedLeft :
    tensorSquareKernelFirstMap S ≫ tensorSquareMixedLeft S hS hproj = 0 := by
  have hT := cochainTensorShortComplexRight_shortExact_of_projective S hS hproj S.X₃
  have : Mono (cochainTensorMap S.f (𝟙 S.X₃)) := hT.mono_f
  apply (cancel_mono (cochainTensorMap S.f (𝟙 S.X₃))).1
  rw [Category.assoc, tensorSquareMixedLeft_inclusion,
    tensorSquareKernelFirstMap_inclusion_assoc, cochainTensorMap_comp, comp_id, S.zero,
    cochainTensorMap_zero_right, zero_comp]

@[simp]
lemma tensorSquareKernelFirstMap_mixedRight :
    tensorSquareKernelFirstMap S ≫ tensorSquareMixedRight S hS hproj = 0 := by
  have hT := cochainTensorShortComplexLeft_shortExact_of_projective S.X₃ S hS hproj
  have : Mono (cochainTensorMap (𝟙 S.X₃) S.f) := hT.mono_f
  apply (cancel_mono (cochainTensorMap (𝟙 S.X₃) S.f)).1
  rw [Category.assoc, tensorSquareMixedRight_inclusion,
    tensorSquareKernelFirstMap_inclusion_assoc, cochainTensorMap_comp, S.zero, comp_id,
    cochainTensorMap_zero_left, zero_comp]

/-- Exchange interchanges the two canonical mixed components with the Koszul symmetry. -/
@[reassoc]
lemma tensorSquareKernelSwap_mixedLeft :
    tensorSquareKernelSwap S.g ≫ tensorSquareMixedLeft S hS hproj =
      tensorSquareMixedRight S hS hproj ≫ (cochainTensorSymmetry S.X₃ S.X₁).hom := by
  have hT := cochainTensorShortComplexRight_shortExact_of_projective S hS hproj S.X₃
  have : Mono (cochainTensorMap S.f (𝟙 S.X₃)) := hT.mono_f
  apply (cancel_mono (cochainTensorMap S.f (𝟙 S.X₃))).1
  calc
    _ = tensorSquareKernelSwap S.g ≫ tensorSquareKernelInclusion S.g ≫
        cochainTensorMap (𝟙 S.X₂) S.g := by
      rw [Category.assoc, tensorSquareMixedLeft_inclusion]
    _ = tensorSquareKernelInclusion S.g ≫ tensorSquareSwap S.X₂ ≫
        cochainTensorMap (𝟙 S.X₂) S.g := by rw [tensorSquareKernelSwap_inclusion_assoc]
    _ = tensorSquareKernelInclusion S.g ≫ cochainTensorMap S.g (𝟙 S.X₂) ≫
        (cochainTensorSymmetry S.X₃ S.X₂).hom := by
      simpa only [Category.assoc] using
        tensorSquareKernelInclusion S.g ≫=
          (cochainTensorSymmetry_naturality S.g (𝟙 S.X₂)).symm
    _ = tensorSquareMixedRight S hS hproj ≫ cochainTensorMap (𝟙 S.X₃) S.f ≫
        (cochainTensorSymmetry S.X₃ S.X₂).hom := by
      simpa only [Category.assoc] using
        ((tensorSquareMixedRight_inclusion S hS hproj) =≫
          (cochainTensorSymmetry S.X₃ S.X₂).hom).symm
    _ = _ := by rw [cochainTensorSymmetry_naturality, Category.assoc]

@[reassoc]
lemma tensorSquareKernelSwap_mixedRight :
    tensorSquareKernelSwap S.g ≫ tensorSquareMixedRight S hS hproj =
      tensorSquareMixedLeft S hS hproj ≫ (cochainTensorSymmetry S.X₁ S.X₃).hom := by
  have h : tensorSquareKernelSwap S.g ≫ tensorSquareMixedLeft S hS hproj ≫
      (cochainTensorSymmetry S.X₁ S.X₃).hom = tensorSquareMixedRight S hS hproj := by
    rw [tensorSquareKernelSwap_mixedLeft_assoc, cochainTensorSymmetry_hom_comp, comp_id]
  rw [← h, ← Category.assoc, tensorSquareKernelSwap_sq, id_comp]

/-- The canonical map from the intermediate layer to the two mixed components. -/
def tensorSquareMixedMap : tensorSquareKernel S.g ⟶
    cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁ :=
  biprod.lift (tensorSquareMixedLeft S hS hproj) (tensorSquareMixedRight S hS hproj)

@[simp]
lemma tensorSquareKernelFirstMap_mixedMap :
    tensorSquareKernelFirstMap S ≫ tensorSquareMixedMap S hS hproj = 0 := by
  apply biprod.hom_ext <;> simp [tensorSquareMixedMap]

/-- The inner short complex of the tensor-square filtration. -/
abbrev tensorSquareMixedShortComplex :=
  ShortComplex.mk (tensorSquareKernelFirstMap S) (tensorSquareMixedMap S hS hproj)
    (tensorSquareKernelFirstMap_mixedMap S hS hproj)

/-- The exchange on the two mixed components. -/
def tensorSquareMixedSwap : cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁ ⟶
    cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁ :=
  biprod.desc ((cochainTensorSymmetry S.X₁ S.X₃).hom ≫ biprod.inr)
    ((cochainTensorSymmetry S.X₃ S.X₁).hom ≫ biprod.inl)

lemma tensorSquareMixedSwap_sq :
    tensorSquareMixedSwap S ≫ tensorSquareMixedSwap S = 𝟙 _ := by
  apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
    simp [tensorSquareMixedSwap, Category.assoc] <;>
    simp [cochainTensorSymmetry_hom_comp]

lemma tensorSquareMixedMap_swap :
    tensorSquareKernelSwap S.g ≫ tensorSquareMixedMap S hS hproj =
      tensorSquareMixedMap S hS hproj ≫ tensorSquareMixedSwap S := by
  apply biprod.hom_ext <;>
    simp [tensorSquareMixedMap, tensorSquareMixedSwap, tensorSquareKernelSwap_mixedLeft,
      tensorSquareKernelSwap_mixedRight]

end Adams
end SerrePositivity
