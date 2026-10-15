module
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import Mathlib.Data.ZMod.Basic

/-! # balanced tensorの各変数のdg関手・単位・合成保存の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (N : LeftModule A D) : DGFunctor A (RightModule A D) (Complex A) :=
  BalancedTensor.rightTensorDG A D N
example (M : RightModule A D) : DGFunctor A (LeftModule A D) (Complex A) :=
  BalancedTensor.leftTensorDG A D M
example (M : RightModule (ZMod 2) PUnit.{1}) :
    DGFunctor (ZMod 2) (LeftModule (ZMod 2) PUnit.{1}) (Complex (ZMod 2)) :=
  BalancedTensor.leftTensorDG (ZMod 2) PUnit.{1} M

#print axioms BalancedTensor.cochain_element_ext
#print axioms BalancedTensor.cochain_zero_element_ext
#print axioms BalancedTensor.homMap_ext
#print axioms BalancedTensor.rightHomMap_element
#print axioms BalancedTensor.leftHomMap_element
#print axioms BalancedTensor.rightHomMap_element_of_sum
#print axioms BalancedTensor.leftHomMap_element_of_sum
#print axioms BalancedTensor.element_units_smul_right
#print axioms BalancedTensor.moduleHom_unit_π
#print axioms BalancedTensor.leftModuleHom_unit_π
#print axioms BalancedTensor.rightHomMap_unit
#print axioms BalancedTensor.leftHomMap_unit
#print axioms BalancedTensor.rightHomMap_forward
#print axioms BalancedTensor.leftModuleHomForward_π
#print axioms BalancedTensor.leftHomMap_forward
#print axioms BalancedTensor.rightTensorDG
#print axioms BalancedTensor.leftTensorDG
