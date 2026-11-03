module
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution

/-! # U8a2：全次数 shift・境界保存・K(D) の整合的 shift -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (s : ℤ)
example : HasShift (ModuleHomotopyCategory A D) ℤ := inferInstance
example : (moduleToHomotopy A D).CommShift ℤ := inferInstance
example (x : D) : (moduleHomotopyEvaluation A D x).CommShift ℤ := inferInstance
example : (moduleQuasiIso A D).IsCompatibleWithShift ℤ := inferInstance
example : (moduleHomotopyQuasiIso A D).IsCompatibleWithShift ℤ := inferInstance
example {M N : ModuleCategory A D} {f g : M ⟶ N} (h : ModuleHomotopy A D f g) :
    Nonempty (ModuleHomotopy A D (f⟦s⟧') (g⟦s⟧')) := moduleHomotopy_shift A D h s
example {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleQuasiIso A D (f⟦s⟧') ↔ moduleQuasiIso A D f := moduleQuasiIso_shift_iff A D f s
example {M N : ModuleHomotopyCategory A D} (f : M ⟶ N) :
    moduleHomotopyQuasiIso A D (f⟦s⟧') ↔ moduleHomotopyQuasiIso A D f :=
  moduleHomotopyQuasiIso_shift_iff A D f s
example (M N : RightModule A D) (x : D) (i : ℤ) (h : (moduleHom A D M N).X (-1)) :
    ((moduleHomπ A D (shiftModule s M) (shiftModule s N) x).f (-1)
      ((moduleShiftHom A D s M N).f (-1) h)).v i (i + (-1)) rfl =
      (s * (-1)).negOnePow • ((moduleHomπ A D M N x).f (-1) h).v
        (i + s) (i + (-1) + s) (by omega) :=
  moduleShiftHom_π_v A D s M N x (-1) i (i + (-1)) rfl h
example : (moduleShiftDG A D s).onClosed = moduleShiftFunctor A D s :=
  moduleShiftDG_onClosed_eq A D s
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.shiftModuleParamTrans
#print axioms SerrePositivity.DifferentialGraded.moduleShiftHom
#print axioms SerrePositivity.DifferentialGraded.moduleShiftHom_π
#print axioms SerrePositivity.DifferentialGraded.moduleShiftHom_π_v
#print axioms SerrePositivity.DifferentialGraded.moduleShiftHom_identity
#print axioms SerrePositivity.DifferentialGraded.moduleShiftHom_comp
#print axioms SerrePositivity.DifferentialGraded.moduleShiftDG
#print axioms SerrePositivity.DifferentialGraded.shiftHom_closedMap
#print axioms SerrePositivity.DifferentialGraded.moduleShiftDG_map_eval
#print axioms SerrePositivity.DifferentialGraded.moduleShiftDG_map_eq
#print axioms SerrePositivity.DifferentialGraded.moduleShiftDG_onClosed_eq
#print axioms SerrePositivity.DifferentialGraded.moduleBoundaryCompatibleWithShift
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopy_shift
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyEvaluationCommShift
#print axioms SerrePositivity.DifferentialGraded.moduleQuasiIso_shift_iff
#print axioms SerrePositivity.DifferentialGraded.moduleQuasiIsoCompatibleWithShift
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyQuasiIso_shift_iff
#print axioms SerrePositivity.DifferentialGraded.moduleHomotopyQuasiIsoCompatibleWithShift
