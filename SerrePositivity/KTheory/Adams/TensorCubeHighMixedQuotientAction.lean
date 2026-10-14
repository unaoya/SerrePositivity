module

public import SerrePositivity.KTheory.Adams.TensorCubeHighMixedQuotient

/-! # The induced cubic action on the high mixed cokernel -/

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
def tensorCubeHighMixedCokernelRotation :
    tensorCubeHighMixedCokernel S hS hproj ⟶ tensorCubeHighMixedCokernel S hS hproj :=
  (tensorCubeHighMixedCokernelIso S hS hproj).hom ≫ tensorCubeHighMixedRotation S ≫
    (tensorCubeHighMixedCokernelIso S hS hproj).inv

set_option maxHeartbeats 600000 in
-- Normalize the chosen cokernel isomorphism when identifying its induced projection.
lemma tensorCubeHighMixedCokernelRotation_π :
    cokernel.π (tensorCubeHighMixedShortComplex S hS hproj).f ≫
      tensorCubeHighMixedCokernelRotation S hS hproj =
      tensorCubeKernelRotation S.g ≫ cokernel.π (tensorCubeHighMixedShortComplex S hS hproj).f :=
  conjugate_projection (cokernel.π (tensorCubeHighMixedShortComplex S hS hproj).f)
    (tensorCubeHighMixedCokernelIso S hS hproj) (tensorCubeHighMixedMap S hS hproj)
    (tensorCubeKernelRotation S.g) (tensorCubeHighMixedRotation S)
    (tensorCubeHighMixedCokernelIso_π_hom S hS hproj)
    (tensorCubeHighMixedMap_rotation S hS hproj)

/-- The projection equation uniquely determines the induced quotient rotation. -/
lemma tensorCubeHighMixedCokernelRotation_unique
    (r : tensorCubeHighMixedCokernel S hS hproj ⟶ tensorCubeHighMixedCokernel S hS hproj)
    (hr : cokernel.π (tensorCubeHighMixedShortComplex S hS hproj).f ≫ r =
      tensorCubeKernelRotation S.g ≫ cokernel.π (tensorCubeHighMixedShortComplex S hS hproj).f) :
    r = tensorCubeHighMixedCokernelRotation S hS hproj := by
  apply (cancel_epi (cokernel.π (tensorCubeHighMixedShortComplex S hS hproj).f)).mp
  exact hr.trans (tensorCubeHighMixedCokernelRotation_π S hS hproj).symm

set_option maxHeartbeats 600000 in
-- Compare the conjugated action with its explicit cokernel model.
lemma tensorCubeHighMixedCokernelRotation_cube :
    tensorCubeHighMixedCokernelRotation S hS hproj ≫
      tensorCubeHighMixedCokernelRotation S hS hproj ≫
      tensorCubeHighMixedCokernelRotation S hS hproj = 𝟙 _ :=
  conjugate_cube (tensorCubeHighMixedCokernelIso S hS hproj) (tensorCubeHighMixedRotation S)
    (tensorCubeHighMixedRotation_cube S)

def tensorCubeHighMixedCokernelAction :
    CochainCubicAction (tensorCubeHighMixedCokernel S hS hproj) :=
  ⟨tensorCubeHighMixedCokernelRotation S hS hproj,
    tensorCubeHighMixedCokernelRotation_cube S hS hproj⟩

set_option maxHeartbeats 600000 in
-- Cancel the two directions of the chosen cokernel comparison.
lemma tensorCubeHighMixedCokernelIso_rotation :
    tensorCubeHighMixedCokernelRotation S hS hproj ≫
      (tensorCubeHighMixedCokernelIso S hS hproj).hom =
      (tensorCubeHighMixedCokernelIso S hS hproj).hom ≫ tensorCubeHighMixedRotation S := by
  simp only [tensorCubeHighMixedCokernelRotation, Category.assoc, Iso.inv_hom_id, comp_id]

end Adams
end SerrePositivity
