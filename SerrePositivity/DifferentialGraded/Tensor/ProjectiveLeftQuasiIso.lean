module
public import SerrePositivity.DifferentialGraded.Tensor.QuasiIsoLeft
public import SerrePositivity.DifferentialGraded.Tensor.ProjectiveKFlat

/-! # 射影的・semifree右加群を固定した左準同型保存 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomotopicallyProjective_preserves_leftQuasiIso {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) {L L' : LeftModuleCategory A D} (g : L ⟶ L')
    (hg : leftModuleQuasiIso A D g) :
    QuasiIso ((BalancedTensor.leftTensorFunctor A D (ForgetEnrichment.to (Complex A) M)).map g) :=
  moduleRelativeKFlat_preserves_leftQuasiIso A D _
    (moduleHomotopicallyProjective_relativeKFlat A D hM) g hg

lemma moduleSemifree_preserves_leftQuasiIso {M : ModuleCategory A D}
    (hM : moduleSemifree A D M) {L L' : LeftModuleCategory A D} (g : L ⟶ L')
    (hg : leftModuleQuasiIso A D g) :
    QuasiIso ((BalancedTensor.leftTensorFunctor A D (ForgetEnrichment.to (Complex A) M)).map g) :=
  moduleRelativeKFlat_preserves_leftQuasiIso A D _ (moduleSemifree_relativeKFlat A D hM) g hg

end SerrePositivity.DifferentialGraded
