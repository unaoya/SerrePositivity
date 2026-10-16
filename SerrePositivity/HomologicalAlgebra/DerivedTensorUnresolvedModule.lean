module
public import SerrePositivity.HomologicalAlgebra.ModuleTensorCochainFiltration
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleModels

/-! # Tensor any bounded-above actual derived object with an unresolved module -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- A fixed projective representative computes tensoring with each unresolved module. -/
def derivedTensorUnresolvedModuleModelIso (M : ModuleCat.{u} R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (P : BoundedAboveDerivedModel X.obj) :
    (boundedAboveDerivedTensor.obj (boundedAboveDerivedSingleFunctor.obj M, X)).obj ≅
      DerivedCategory.Q.obj ((moduleTensorCochainFunctor P.complex).obj M) := by
  have := moduleResolutionTensorAugmentation_quasiIso M P
  exact boundedAboveDerivedTensorModelIso _ _
      (projectiveResolutionDerivedModel (projectiveResolution M)) P ≪≫
    asIso (DerivedCategory.Q.map (cochainTensorMap
      (projectiveResolutionCochainAugmentation (projectiveResolution M)) (𝟙 P.complex))) ≪≫
    DerivedCategory.Q.mapIso (cochainTensorSingleLeftIso M P.complex)

end SerrePositivity
