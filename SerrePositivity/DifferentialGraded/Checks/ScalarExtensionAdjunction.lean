module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.BalancedTensor
public import Mathlib.Data.ZMod.Basic

/-! # 非 flat な係数変更に対する dg 加群随伴の検査 -/
@[expose] public section
noncomputable section
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory

example : moduleExtension (Int.castRingHom (ZMod 2)) PUnit ⊣
    moduleRestriction (Int.castRingHom (ZMod 2)) PUnit :=
  moduleAdjunction (Int.castRingHom (ZMod 2)) PUnit

#print axioms moduleUnit_family_naturality
#print axioms moduleUnitApp
#print axioms moduleUnit
#print axioms moduleCounit_family_naturality
#print axioms moduleCounitApp
#print axioms moduleCounit
#print axioms module_left_triangle
#print axioms module_right_triangle
#print axioms moduleAdjunction

end SerrePositivity.DifferentialGraded.ScalarExtension
