module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.BalancedTensor
public import Mathlib.Data.ZMod.Basic

/-! # 非 flat な係数変更と相対 tensor の検査 -/
@[expose] public section
noncomputable section
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory

example (M : RightModule ℤ PUnit) (N : LeftModule ℤ PUnit) :
    (extension (Int.castRingHom (ZMod 2))).obj (BalancedTensor.obj ℤ PUnit M N) ≅
      BalancedTensor.obj (ZMod 2) (DGBaseChange (Int.castRingHom (ZMod 2)) PUnit)
        (rightModule (Int.castRingHom (ZMod 2)) PUnit M)
        (leftModule (Int.castRingHom (ZMod 2)) PUnit N) :=
  balancedIso (Int.castRingHom (ZMod 2)) PUnit M N

#print axioms leftModule_action
#print axioms rightAction_comparison
#print axioms leftAction_comparison
#print axioms generatorIso
#print axioms relationIso
#print axioms relationLeft_square
#print axioms relationRight_square
#print axioms balancedPresentationIso
#print axioms balancedIso
#print axioms balancedIso_projection
#print axioms balancedIso_ι
#print axioms balancedIso_inv_ι
#print axioms extendedBalanced_hom_ext
#print axioms extended_rightAction_family
#print axioms extended_leftAction_family
#print axioms balancedIso_naturality

end SerrePositivity.DifferentialGraded.ScalarExtension
