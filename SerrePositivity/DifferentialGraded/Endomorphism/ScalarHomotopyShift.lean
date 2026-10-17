module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarShiftAddition
public import SerrePositivity.DifferentialGraded.Module.ShiftHomotopy

/-! # 実際の係数拡大の整合的shift比較を主Kへ降ろす -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

@[instance_reducible]
def scalarModuleExtensionHomotopyCommShift :
    (scalarModuleExtensionHomotopy φ D).CommShift ℤ := by
  letI := scalarModuleExtensionCommShift φ D
  unfold scalarModuleExtensionHomotopy
  infer_instance

def scalarModuleExtensionHomotopyFacIso :
    moduleToHomotopy A D ⋙ scalarModuleExtensionHomotopy φ D ≅
      ScalarExtension.moduleExtension φ D ⋙
        moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D) :=
  Quotient.lift.isLift _ _ _

lemma scalarModuleExtensionHomotopyFacIso_commShift :
    letI := scalarModuleExtensionCommShift φ D
    letI := scalarModuleExtensionHomotopyCommShift φ D
    NatTrans.CommShift (scalarModuleExtensionHomotopyFacIso φ D).hom ℤ := by
  let := scalarModuleExtensionCommShift φ D
  let := scalarModuleExtensionHomotopyCommShift φ D
  unfold scalarModuleExtensionHomotopyFacIso
  exact Quotient.liftCommShift_compatibility _ _ _ _

end SerrePositivity.DifferentialGraded
