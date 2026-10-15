module
public import SerrePositivity.PerfectComplex.CubicActionTransport

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
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

/-- Transport the mixed action to the cokernel, with its induced projection equation. -/
def tensorCubeHighMixedCokernelRotation :
    tensorCubeHighMixedCokernel S hS hproj ⟶ tensorCubeHighMixedCokernel S hS hproj :=
  (CochainCubicAction.comapIso (tensorCubeHighMixedCokernelIso S hS hproj)
    ⟨tensorCubeHighMixedRotation S, tensorCubeHighMixedRotation_cube S⟩).map

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
  (CochainCubicAction.comapIso (tensorCubeHighMixedCokernelIso S hS hproj)
    ⟨tensorCubeHighMixedRotation S, tensorCubeHighMixedRotation_cube S⟩).cube

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
  exact CochainCubicAction.comapIso_hom (tensorCubeHighMixedCokernelIso S hS hproj) _

end Adams
end SerrePositivity
