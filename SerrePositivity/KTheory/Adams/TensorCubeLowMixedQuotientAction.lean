module

public import SerrePositivity.KTheory.Adams.TensorCubeLowMixedSupport
public import SerrePositivity.KTheory.Adams.TensorCubeLowMixedRotation

/-! # The induced cubic action on the low mixed cokernel -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
namespace Adams
private lemma conjugate_cube {C : Type*} [Category C] {Q L : C}
    (e : Q ≅ L) (t : L ⟶ L) (ht : t ≫ t ≫ t = 𝟙 L) :
    (e.hom ≫ t ≫ e.inv) ≫ (e.hom ≫ t ≫ e.inv) ≫ (e.hom ≫ t ≫ e.inv) = 𝟙 Q := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc, id_comp, Iso.hom_inv_id] using e.hom ≫= (ht =≫ e.inv)

private lemma conjugate_projection {C : Type*} [Category C] {K Q L : C}
    (p : K ⟶ Q) (e : Q ≅ L) (g : K ⟶ L) (s : K ⟶ K) (t : L ⟶ L)
    (he : p ≫ e.hom = g) (hg : s ≫ g = g ≫ t) :
    p ≫ (e.hom ≫ t ≫ e.inv) = s ≫ p := by
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, comp_id]
  rw [← Category.assoc p e.hom, he, hg]

variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

/-- Transport the mixed action to the cokernel, with its induced projection equation. -/
def tensorCubeLowMixedCokernelRotation :
    cokernel (tensorCubeFirstLayerFirstMap S) ⟶ cokernel (tensorCubeFirstLayerFirstMap S) :=
  (tensorCubeLowMixedCokernelIso S hS hproj).hom ≫ tensorCubeLowMixedRotation S ≫
    (tensorCubeLowMixedCokernelIso S hS hproj).inv

set_option maxHeartbeats 600000 in
-- Normalize the chosen cokernel isomorphism when identifying its induced projection.
lemma tensorCubeLowMixedCokernelRotation_π :
    cokernel.π (tensorCubeFirstLayerFirstMap S) ≫ tensorCubeLowMixedCokernelRotation S hS hproj =
      tensorCubeFirstLayerRotation S.g ≫ cokernel.π (tensorCubeFirstLayerFirstMap S) :=
  conjugate_projection (cokernel.π (tensorCubeFirstLayerFirstMap S))
    (tensorCubeLowMixedCokernelIso S hS hproj) (tensorCubeLowMixedMap S hS hproj)
    (tensorCubeFirstLayerRotation S.g) (tensorCubeLowMixedRotation S)
    (tensorCubeLowMixedCokernelIso_π_hom S hS hproj)
    (tensorCubeLowMixedMap_rotation S hS hproj)

/-- The projection equation uniquely determines the induced quotient rotation. -/
lemma tensorCubeLowMixedCokernelRotation_unique
    (r : cokernel (tensorCubeFirstLayerFirstMap S) ⟶ cokernel (tensorCubeFirstLayerFirstMap S))
    (hr : cokernel.π (tensorCubeFirstLayerFirstMap S) ≫ r =
      tensorCubeFirstLayerRotation S.g ≫ cokernel.π (tensorCubeFirstLayerFirstMap S)) :
    r = tensorCubeLowMixedCokernelRotation S hS hproj := by
  apply (cancel_epi (cokernel.π (tensorCubeFirstLayerFirstMap S))).mp
  exact hr.trans (tensorCubeLowMixedCokernelRotation_π S hS hproj).symm

set_option maxHeartbeats 600000 in
-- Compare the conjugated action with its explicit cokernel model.
lemma tensorCubeLowMixedCokernelRotation_cube :
    tensorCubeLowMixedCokernelRotation S hS hproj ≫ tensorCubeLowMixedCokernelRotation S hS hproj ≫
      tensorCubeLowMixedCokernelRotation S hS hproj = 𝟙 _ :=
  conjugate_cube (tensorCubeLowMixedCokernelIso S hS hproj) (tensorCubeLowMixedRotation S)
    (tensorCubeLowMixedRotation_cube S)

def tensorCubeLowMixedCokernelAction :
    CochainCubicAction (cokernel (tensorCubeFirstLayerFirstMap S)) :=
  ⟨tensorCubeLowMixedCokernelRotation S hS hproj,
    tensorCubeLowMixedCokernelRotation_cube S hS hproj⟩

set_option maxHeartbeats 600000 in
-- Cancel the two directions of the chosen cokernel comparison.
lemma tensorCubeLowMixedCokernelIso_rotation :
    tensorCubeLowMixedCokernelRotation S hS hproj ≫
      (tensorCubeLowMixedCokernelIso S hS hproj).hom =
      (tensorCubeLowMixedCokernelIso S hS hproj).hom ≫ tensorCubeLowMixedRotation S := by
  simp only [tensorCubeLowMixedCokernelRotation, Category.assoc, Iso.inv_hom_id, comp_id]

end Adams
end SerrePositivity
