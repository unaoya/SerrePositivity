module
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 任意可換環と独立対象宇宙における左準同型保存の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {L L' : LeftModuleCategory A D} (g : L ⟶ L')
    (hg : ∀ x : D, QuasiIso ((leftModuleEvaluation A D x).map g))
    (M : RightModule A D) (hM : moduleRelativeKFlat A D M) :
    QuasiIso ((BalancedTensor.leftTensorFunctor A D M).map g) :=
  moduleRelativeKFlat_preserves_leftQuasiIso A D M hM g ((leftModuleQuasiIso_iff A D g).2 hg)

example {M : ModuleCategory (ZMod 2) PUnit.{1}}
    (hM : moduleSemifree (ZMod 2) PUnit.{1} M)
    {L L' : LeftModuleCategory (ZMod 2) PUnit.{1}} (g : L ⟶ L')
    (hg : leftModuleQuasiIso (ZMod 2) PUnit.{1} g) :
    QuasiIso ((BalancedTensor.leftTensorFunctor (ZMod 2) PUnit.{1}
      (ForgetEnrichment.to (Complex (ZMod 2)) M)).map g) :=
  moduleSemifree_preserves_leftQuasiIso (ZMod 2) PUnit.{1} hM g hg

#print axioms leftModuleQuasiIso
#print axioms leftModuleQuasiIso_iff
#print axioms leftModuleQuasiIsoIsMultiplicative
#print axioms leftModuleQuasiIsoHasTwoOutOfThree
#print axioms leftModuleQuasiIsoStableUnderRetracts
#print axioms leftModuleQuasiIsoRespectsIso
#print axioms moduleRelativeKFlat_opposite_test
#print axioms moduleRelativeKFlat_preserves_leftQuasiIso
#print axioms moduleHomotopicallyProjective_preserves_leftQuasiIso
#print axioms moduleSemifree_preserves_leftQuasiIso
