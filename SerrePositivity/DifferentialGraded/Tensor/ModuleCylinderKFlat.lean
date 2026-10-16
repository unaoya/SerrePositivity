module
public import SerrePositivity.DifferentialGraded.Tensor.TensorModuleIso
public import SerrePositivity.DifferentialGraded.Tensor.KFlatComplex
public import SerrePositivity.DifferentialGraded.Module.Cylinder

/-! # K-flat複体とのtensorとdg加群cylinderの相対K-flat性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A]

lemma complexKFlat_interval : complexKFlat A (dgInterval A) := by
  intro L hL
  exact cochainAcyclic_of_homotopyEquiv (complexKFlat_unit A L hL)
    (tensorIntervalHomotopyEquiv A L).symm

variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRelativeKFlat_tensor (K : Complex A) (hK : complexKFlat A K)
    (M : RightModule A D) (hM : moduleRelativeKFlat A D M) :
    moduleRelativeKFlat A D (tensorModule K M) := by
  intro N hN
  exact cochainAcyclic_of_iso (hK _ (hM N hN)) (BalancedTensor.tensorModuleIso A D K M N).symm

lemma modulePrecylinder_relativeKFlat (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) (modulePrecylinder A D M).I) :=
  moduleRelativeKFlat_tensor A D (dgInterval A) (complexKFlat_interval A) _ hM

end SerrePositivity.DifferentialGraded
