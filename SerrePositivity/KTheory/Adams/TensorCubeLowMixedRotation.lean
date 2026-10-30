module
public import SerrePositivity.CategoryTheory.Triangulated.Idempotent

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
