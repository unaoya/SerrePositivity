module

public import SerrePositivity.KTheory.Adams.TensorCubeLowMixed
public import Mathlib.CategoryTheory.CommSq

/-! # Structural inclusions of the three low mixed quotient components -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

attribute [reassoc] tensorCubeRotation_cube

@[reassoc]
lemma tensorCubeLowMixed1_inclusion :
    tensorCubeLowMixed1 S hS hproj ≫ cochainTensorTripleMap S.f (𝟙 S.X₃) S.f =
      tensorCubeFirstLayerInclusion S.g ≫ cochainTensorTripleMap (𝟙 S.X₂) S.g (𝟙 S.X₂) := by
  simp only [tensorCubeLowMixed1, Category.assoc]
  rw [← cochainTensorRotation_naturality (𝟙 S.X₃) S.f S.f,
    ← Category.assoc (tensorCubeLowMixed0 S hS hproj), tensorCubeLowMixed0_inclusion]
  simp only [Category.assoc]
  have hs : CommSq (tensorCubeFirstLayerRotation S.g) (tensorCubeFirstLayerInclusion S.g)
      (tensorCubeFirstLayerInclusion S.g) (tensorCubeRotation S.X₂) :=
    ⟨tensorCubeFirstLayerRotation_inclusion S.g⟩
  have hi := (hs.horiz_comp hs).w
  have hh : tensorCubeFirstLayerRotation S.g ≫ tensorCubeFirstLayerRotation S.g ≫
      tensorCubeFirstLayerInclusion S.g ≫ cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) ≫
      (cochainTensorRotationIso S.X₃ S.X₂ S.X₂).hom =
      tensorCubeFirstLayerInclusion S.g ≫ tensorCubeRotation S.X₂ ≫ tensorCubeRotation S.X₂ ≫
        cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) ≫
        (cochainTensorRotationIso S.X₃ S.X₂ S.X₂).hom := by
    simpa only [Category.assoc] using hi =≫
      (cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) ≫
        (cochainTensorRotationIso S.X₃ S.X₂ S.X₂).hom)
  refine hh.trans ?_
  rw [cochainTensorRotation_naturality S.g (𝟙 S.X₂) (𝟙 S.X₂)]
  simp only [tensorCubeRotation_cube_assoc]

set_option maxHeartbeats 400000 in
-- Two transported rotations require comparisons of iterated tensor and kernel instances.
@[reassoc]
lemma tensorCubeLowMixed2_inclusion :
    tensorCubeLowMixed2 S hS hproj ≫ cochainTensorTripleMap S.f S.f (𝟙 S.X₃) =
      tensorCubeFirstLayerInclusion S.g ≫ cochainTensorTripleMap (𝟙 S.X₂) (𝟙 S.X₂) S.g := by
  simp only [tensorCubeLowMixed2, Category.assoc]
  rw [← cochainTensorRotation_naturality S.f (𝟙 S.X₃) S.f,
    ← cochainTensorRotation_naturality_assoc (𝟙 S.X₃) S.f S.f,
    ← Category.assoc (tensorCubeLowMixed0 S hS hproj), tensorCubeLowMixed0_inclusion]
  simp only [Category.assoc]
  have hi := tensorCubeFirstLayerRotation_inclusion S.g
  have hh : tensorCubeFirstLayerRotation S.g ≫ tensorCubeFirstLayerInclusion S.g ≫
      cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) ≫
      (cochainTensorRotationIso S.X₃ S.X₂ S.X₂).hom ≫
      (cochainTensorRotationIso S.X₂ S.X₃ S.X₂).hom =
      tensorCubeFirstLayerInclusion S.g ≫ tensorCubeRotation S.X₂ ≫
        cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) ≫
        (cochainTensorRotationIso S.X₃ S.X₂ S.X₂).hom ≫
        (cochainTensorRotationIso S.X₂ S.X₃ S.X₂).hom := by
    simpa only [Category.assoc] using hi =≫
      (cochainTensorTripleMap S.g (𝟙 S.X₂) (𝟙 S.X₂) ≫
        (cochainTensorRotationIso S.X₃ S.X₂ S.X₂).hom ≫
        (cochainTensorRotationIso S.X₂ S.X₃ S.X₂).hom)
  refine hh.trans ?_
  rw [cochainTensorRotation_naturality_assoc S.g (𝟙 S.X₂) (𝟙 S.X₂),
    cochainTensorRotation_naturality (𝟙 S.X₂) S.g (𝟙 S.X₂)]
  simp only [tensorCubeRotation_cube_assoc]

include hS hproj in
lemma tensorCubeLowMixed1_target_inclusion_mono :
    Mono (cochainTensorTripleMap S.f (𝟙 S.X₃) S.f) := by
  have := tensorCubeLowMixed0_target_inclusion_mono S hS hproj
  have he := cochainTensorRotation_naturality (𝟙 S.X₃) S.f S.f
  have hh : (cochainTensorRotationIso S.X₃ S.X₁ S.X₁).inv ≫
      cochainTensorTripleMap (𝟙 S.X₃) S.f S.f ≫
      (cochainTensorRotationIso S.X₃ S.X₂ S.X₂).hom =
      cochainTensorTripleMap S.f (𝟙 S.X₃) S.f := by
    rw [he]
    simp only [Iso.inv_hom_id_assoc]
  rw [← hh]
  infer_instance

include hS hproj in
lemma tensorCubeLowMixed2_target_inclusion_mono :
    Mono (cochainTensorTripleMap S.f S.f (𝟙 S.X₃)) := by
  have := tensorCubeLowMixed1_target_inclusion_mono S hS hproj
  have he := cochainTensorRotation_naturality S.f (𝟙 S.X₃) S.f
  have hh : (cochainTensorRotationIso S.X₁ S.X₃ S.X₁).inv ≫
      cochainTensorTripleMap S.f (𝟙 S.X₃) S.f ≫
      (cochainTensorRotationIso S.X₂ S.X₃ S.X₂).hom =
      cochainTensorTripleMap S.f S.f (𝟙 S.X₃) := by
    rw [he]
    simp only [Iso.inv_hom_id_assoc]
  rw [← hh]
  infer_instance

end Adams
end SerrePositivity
