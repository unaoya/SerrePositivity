module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.BalancedTensor
public import Mathlib.Data.ZMod.Basic

/-! # 左加群の係数拡大と一対象 tensor 比較の検査 -/
@[expose] public section
noncomputable section
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory

example : LeftModuleCategory ℤ PUnit ⥤
    LeftModuleCategory (ZMod 2) (DGBaseChange (Int.castRingHom (ZMod 2)) PUnit) :=
  leftModuleExtension (Int.castRingHom (ZMod 2)) PUnit

#print axioms leftModuleExtension
#print axioms balancedIso_module_naturality
#print axioms ringBalancedIso
#print axioms ι_ringBalancedIso
#print axioms ringBalancedIso_comparison
#print axioms ringComplexBaseChange_comparison

end SerrePositivity.DifferentialGraded.ScalarExtension
