module
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 相対K-flatの準同型保存判定と左零対象の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (M : RightModule A D)
    (h : ∀ {L L' : LeftModuleCategory A D} (g : L ⟶ L'), leftModuleQuasiIso A D g →
      QuasiIso ((BalancedTensor.leftTensorFunctor A D M).map g)) :
    moduleRelativeKFlat A D M :=
  (moduleRelativeKFlat_iff_preserves_leftQuasiIso A D M).2 h

example : IsZero (leftModuleZero A D) := leftModuleZero_isZero A D

example (M : RightModule (ZMod 2) PUnit.{1}) :
    moduleRelativeKFlat (ZMod 2) PUnit.{1} M ↔
      ∀ {L L' : LeftModuleCategory (ZMod 2) PUnit.{1}} (g : L ⟶ L'),
        leftModuleQuasiIso (ZMod 2) PUnit.{1} g →
          QuasiIso ((BalancedTensor.leftTensorFunctor (ZMod 2) PUnit.{1} M).map g) :=
  moduleRelativeKFlat_iff_preserves_leftQuasiIso (ZMod 2) PUnit.{1} M

#print axioms leftModuleZero
#print axioms leftModuleZero_isZero
#print axioms leftModuleHasZeroObject
#print axioms leftModuleEvaluationAdditive
#print axioms leftModuleZero_evaluation_isZero
#print axioms moduleRelativeKFlat_iff_preserves_leftQuasiIso
#print axioms moduleRelativeKFlat_zero
