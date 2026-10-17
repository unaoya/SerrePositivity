module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionModule
public import Mathlib.Data.ZMod.Basic

/-! # 全次数 Hom と dg 加群の係数変更の検査 -/
@[expose] public section
noncomputable section
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory

example (M : RightModule ℤ PUnit) :
    RightModule (ZMod 2) (DGBaseChange (Int.castRingHom (ZMod 2)) PUnit) :=
  rightModule (Int.castRingHom (ZMod 2)) PUnit M

example (M : LeftModule ℤ PUnit) :
    LeftModule (ZMod 2) (DGBaseChange (Int.castRingHom (ZMod 2)) PUnit) :=
  leftModule (Int.castRingHom (ZMod 2)) PUnit M

#print axioms homComparison
#print axioms tensorIso_inv_apply
#print axioms homComparison_apply
#print axioms sphereIso_inv_one
#print axioms homComparison_identity
#print axioms homComparison_composition
#print axioms complexDGFunctor
#print axioms tensorIso_braiding
#print axioms oppositeDGFunctor
#print axioms rightModule
#print axioms leftModule
#print axioms rightModule_action

end SerrePositivity.DifferentialGraded.ScalarExtension
