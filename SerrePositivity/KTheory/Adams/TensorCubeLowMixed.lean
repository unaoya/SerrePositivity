module

public import SerrePositivity.KTheory.Adams.TensorCubeFirstLayerSplitting

/-! # Canonical quotient maps to the low mixed tensor-cube components -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
namespace Adams
private lemma comp_twice_equivariant_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {A K M N : C} (i : A ⟶ K) (τA : A ⟶ A) (τK : K ⟶ K)
    (x : K ⟶ M) (z : M ⟶ N) (hc : i ≫ τK = τA ≫ i) (hz : i ≫ x = 0) :
    i ≫ τK ≫ τK ≫ x ≫ z = 0 := by
  calc
    _ = τA ≫ i ≫ τK ≫ x ≫ z := by
      simpa only [Category.assoc] using hc =≫ (τK ≫ x ≫ z)
    _ = τA ≫ τA ≫ i ≫ x ≫ z := by
      simpa only [Category.assoc] using τA ≫= (hc =≫ (x ≫ z))
    _ = 0 := by
      rw [← Category.assoc i x z, hz]
      simp only [zero_comp, comp_zero]

variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

/-- Extract the first quotient factor, then lift the second factor into A. -/
def tensorCubeLowMixed0Partial : tensorCubeFirstLayer S.g ⟶
    cochainTensor (cochainTensor S.X₃ S.X₁) S.X₂ := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  have hT := cochainTensorTripleShortComplexSecond_shortExact S.X₃ S σ S.X₂
  have := hT.mono_f
  exact hT.exact.lift (tensorCubeFirstLayerInclusion S.g ≫
    cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂)) (by
      change (tensorCubeFirstLayerInclusion S.g ≫
        cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂)) ≫
        cochainTensorTripleMap (𝟙 S.X₃) S.g (𝟙 S.X₂) = 0
      simp only [Category.assoc, cochainTensorTripleMap, cochainTensorMap_comp,
        comp_id, id_comp]
      exact tensorCubeFirstLayerInclusion_pair0 S.g)

@[reassoc]
lemma tensorCubeLowMixed0Partial_inclusion :
    tensorCubeLowMixed0Partial S hS hproj ≫ cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₂) =
      tensorCubeFirstLayerInclusion S.g ≫ cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) := by
  dsimp [tensorCubeLowMixed0Partial]
  exact Fork.IsLimit.lift_ι _

lemma tensorCubeLowMixed0Partial_quotient_zero :
    tensorCubeLowMixed0Partial S hS hproj ≫
      cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₁) S.g = 0 := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  have hT := cochainTensorTripleShortComplexSecond_shortExact S.X₃ S σ S.X₃
  have : Mono (cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₃)) := hT.mono_f
  apply (cancel_mono (cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₃))).mp
  have he : cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₁) S.g ≫
      cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₃) =
      cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₂) ≫
      cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₂) S.g := by
    simp only [cochainTensorTripleMap, cochainTensorMap_comp, comp_id, id_comp]
  rw [Category.assoc, he, ← Category.assoc, tensorCubeLowMixed0Partial_inclusion,
    Category.assoc]
  simp only [cochainTensorTripleMap, cochainTensorMap_comp, comp_id, id_comp, zero_comp]
  exact tensorCubeFirstLayerInclusion_pair2 S.g

/-- Extract the DAA mixed component by lifting once more in the third position. -/
def tensorCubeLowMixed0 : tensorCubeFirstLayer S.g ⟶
    cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁ := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  have hT := cochainTensorTripleShortComplexThird_shortExact S.X₃ S.X₁ S σ
  have := hT.mono_f
  exact hT.exact.lift (tensorCubeLowMixed0Partial S hS hproj) (by
    have hz := tensorCubeLowMixed0Partial_quotient_zero S hS hproj
    simp only [cochainTensorTripleMap, cochainTensorMap_id] at hz
    exact hz)

@[reassoc]
lemma tensorCubeLowMixed0_third_inclusion :
    tensorCubeLowMixed0 S hS hproj ≫ cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₁) S.f =
      tensorCubeLowMixed0Partial S hS hproj := by
  rw [cochainTensorTripleMap, cochainTensorMap_id]
  dsimp [tensorCubeLowMixed0]
  exact Fork.IsLimit.lift_ι _

@[reassoc]
lemma tensorCubeLowMixed0_inclusion :
    tensorCubeLowMixed0 S hS hproj ≫ cochainTensorTripleMap (𝟙 S.X₃) S.f S.f =
      tensorCubeFirstLayerInclusion S.g ≫ cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) := by
  have he : cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₁) S.f ≫
      cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₂) =
      cochainTensorTripleMap (𝟙 S.X₃) S.f S.f := by
    simp only [cochainTensorTripleMap, cochainTensorMap_comp, comp_id, id_comp]
  rw [← he, ← Category.assoc, tensorCubeLowMixed0_third_inclusion,
    tensorCubeLowMixed0Partial_inclusion]

include hS hproj in
lemma tensorCubeLowMixed0_target_inclusion_mono :
    Mono (cochainTensorTripleMap (𝟙 S.X₃) S.f S.f) := by
  let σ := cochainDegreewiseSplittingOfProjective S hS hproj
  have h2 := cochainTensorTripleShortComplexSecond_shortExact S.X₃ S σ S.X₂
  have h3 := cochainTensorTripleShortComplexThird_shortExact S.X₃ S.X₁ S σ
  have : Mono (cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₂)) := h2.mono_f
  have : Mono (cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₁) S.f) := by
    rw [cochainTensorTripleMap, cochainTensorMap_id]
    exact h3.mono_f
  have he : cochainTensorTripleMap (𝟙 S.X₃) (𝟙 S.X₁) S.f ≫
      cochainTensorTripleMap (𝟙 S.X₃) S.f (𝟙 S.X₂) =
      cochainTensorTripleMap (𝟙 S.X₃) S.f S.f := by
    simp only [cochainTensorTripleMap, cochainTensorMap_comp, comp_id, id_comp]
  rw [← he]
  infer_instance

@[simp]
lemma tensorCubeFirstLayerFirstMap_lowMixed0 :
    tensorCubeFirstLayerFirstMap S ≫ tensorCubeLowMixed0 S hS hproj = 0 := by
  have := tensorCubeLowMixed0_target_inclusion_mono S hS hproj
  apply (cancel_mono (cochainTensorTripleMap (𝟙 S.X₃) S.f S.f)).mp
  rw [Category.assoc, tensorCubeLowMixed0_inclusion,
    tensorCubeFirstLayerFirstMap_inclusion_assoc]
  simp only [tensorCubeMap, cochainTensorTripleMap, cochainTensorMap_comp,
    S.zero, comp_id, cochainTensorMap_zero_left, zero_comp]

attribute [reassoc] tensorCubeFirstLayerRotation_cube cochainTensorRotation_cube
attribute [reassoc] tensorCubeFirstLayerFirstMap_lowMixed0

/-- The ADA component is the transported first mixed quotient map. -/
def tensorCubeLowMixed1 : tensorCubeFirstLayer S.g ⟶
    cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁ :=
  tensorCubeFirstLayerRotation S.g ≫ tensorCubeFirstLayerRotation S.g ≫
    tensorCubeLowMixed0 S hS hproj ≫ (cochainTensorRotationIso S.X₃ S.X₁ S.X₁).hom

/-- The AAD component is obtained by one rotation on the source and two on the target. -/
def tensorCubeLowMixed2 : tensorCubeFirstLayer S.g ⟶
    cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃ :=
  tensorCubeFirstLayerRotation S.g ≫ tensorCubeLowMixed0 S hS hproj ≫
    (cochainTensorRotationIso S.X₃ S.X₁ S.X₁).hom ≫
    (cochainTensorRotationIso S.X₁ S.X₃ S.X₁).hom

@[reassoc]
lemma tensorCubeFirstLayerRotation_lowMixed0 :
    tensorCubeFirstLayerRotation S.g ≫ tensorCubeLowMixed0 S hS hproj =
      tensorCubeLowMixed2 S hS hproj ≫ (cochainTensorRotationIso S.X₁ S.X₁ S.X₃).hom := by
  simp only [tensorCubeLowMixed2, Category.assoc, cochainTensorRotation_cube, comp_id]

@[reassoc]
lemma tensorCubeFirstLayerRotation_lowMixed1 :
    tensorCubeFirstLayerRotation S.g ≫ tensorCubeLowMixed1 S hS hproj =
      tensorCubeLowMixed0 S hS hproj ≫ (cochainTensorRotationIso S.X₃ S.X₁ S.X₁).hom := by
  simp only [tensorCubeLowMixed1, tensorCubeFirstLayerRotation_cube_assoc]

@[reassoc]
lemma tensorCubeFirstLayerRotation_lowMixed2 :
    tensorCubeFirstLayerRotation S.g ≫ tensorCubeLowMixed2 S hS hproj =
      tensorCubeLowMixed1 S hS hproj ≫ (cochainTensorRotationIso S.X₁ S.X₃ S.X₁).hom := by
  simp only [tensorCubeLowMixed1, tensorCubeLowMixed2, Category.assoc]

/-- All three low mixed quotient maps combined. -/
def tensorCubeLowMixedMap : tensorCubeFirstLayer S.g ⟶
    cochainTensor (cochainTensor S.X₃ S.X₁) S.X₁ ⊞
      (cochainTensor (cochainTensor S.X₁ S.X₃) S.X₁ ⊞
        cochainTensor (cochainTensor S.X₁ S.X₁) S.X₃) :=
  biprod.lift (tensorCubeLowMixed0 S hS hproj)
    (biprod.lift (tensorCubeLowMixed1 S hS hproj) (tensorCubeLowMixed2 S hS hproj))

@[simp]
lemma tensorCubeFirstLayerFirstMap_lowMixed1 :
    tensorCubeFirstLayerFirstMap S ≫ tensorCubeLowMixed1 S hS hproj = 0 := by
  change tensorCubeFirstLayerFirstMap S ≫ tensorCubeFirstLayerRotation S.g ≫
    tensorCubeFirstLayerRotation S.g ≫ tensorCubeLowMixed0 S hS hproj ≫
      (cochainTensorRotationIso S.X₃ S.X₁ S.X₁).hom = 0
  exact comp_twice_equivariant_zero _ _ _ _ _
    (tensorCubeFirstLayerFirstMap_rotation S) (tensorCubeFirstLayerFirstMap_lowMixed0 S hS hproj)

@[simp]
lemma tensorCubeFirstLayerFirstMap_lowMixed2 :
    tensorCubeFirstLayerFirstMap S ≫ tensorCubeLowMixed2 S hS hproj = 0 := by
  rw [tensorCubeLowMixed2, ← Category.assoc, tensorCubeFirstLayerFirstMap_rotation]
  simp only [Category.assoc]
  rw [tensorCubeFirstLayerFirstMap_lowMixed0_assoc S hS hproj]
  simp only [zero_comp, comp_zero]

@[simp]
lemma tensorCubeFirstLayerFirstMap_lowMixedMap :
    tensorCubeFirstLayerFirstMap S ≫ tensorCubeLowMixedMap S hS hproj = 0 := by
  apply biprod.hom_ext
  · simp only [Category.assoc, tensorCubeLowMixedMap, biprod.lift_fst, zero_comp,
      tensorCubeFirstLayerFirstMap_lowMixed0]
  · apply biprod.hom_ext
    · simp only [Category.assoc, tensorCubeLowMixedMap, biprod.lift_snd_assoc,
        biprod.lift_fst, zero_comp, tensorCubeFirstLayerFirstMap_lowMixed1]
    · simp only [Category.assoc, tensorCubeLowMixedMap, biprod.lift_snd,
        zero_comp, tensorCubeFirstLayerFirstMap_lowMixed2]

abbrev tensorCubeLowMixedShortComplex :=
  ShortComplex.mk (tensorCubeFirstLayerFirstMap S) (tensorCubeLowMixedMap S hS hproj)
    (tensorCubeFirstLayerFirstMap_lowMixedMap S hS hproj)

end Adams
end SerrePositivity
