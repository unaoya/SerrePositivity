module

public import SerrePositivity.KTheory.Adams.TensorCubeLowMixedSections
public import SerrePositivity.PerfectComplex.TensorTripleCyclicSum

/-! # Equivariance of the low mixed tensor-cube quotient -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
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

variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))

abbrev tensorCubeLowMixedRotation : tensorCubeLowMixedTarget S ⟶ tensorCubeLowMixedTarget S :=
  cochainTensorCyclicSumRotation S.X₃ S.X₁ S.X₁

lemma tensorCubeLowMixedRotation_cube :
    tensorCubeLowMixedRotation S ≫ tensorCubeLowMixedRotation S ≫
      tensorCubeLowMixedRotation S = 𝟙 _ :=
  cochainTensorCyclicSumRotation_cube S.X₃ S.X₁ S.X₁

abbrev tensorCubeLowMixedAction : CochainCubicAction (tensorCubeLowMixedTarget S) :=
  cochainTensorCyclicSumAction S.X₃ S.X₁ S.X₁

set_option maxHeartbeats 600000 in
-- Compare the combined maps through the evaluated nested-kernel and biproduct models.
lemma tensorCubeLowMixedMap_rotation (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) :
    tensorCubeFirstLayerRotation S.g ≫ tensorCubeLowMixedMap S hS hproj =
      tensorCubeLowMixedMap S hS hproj ≫ tensorCubeLowMixedRotation S := by
  exact three_components_rotation (tensorCubeFirstLayerRotation S.g)
    (tensorCubeLowMixed0 S hS hproj) (tensorCubeLowMixed1 S hS hproj)
    (tensorCubeLowMixed2 S hS hproj) (cochainTensorRotationIso S.X₃ S.X₁ S.X₁).hom
    (cochainTensorRotationIso S.X₁ S.X₃ S.X₁).hom
    (cochainTensorRotationIso S.X₁ S.X₁ S.X₃).hom
    (tensorCubeFirstLayerRotation_lowMixed0 S hS hproj)
    (tensorCubeFirstLayerRotation_lowMixed1 S hS hproj)
    (tensorCubeFirstLayerRotation_lowMixed2 S hS hproj)

end Adams
end SerrePositivity
