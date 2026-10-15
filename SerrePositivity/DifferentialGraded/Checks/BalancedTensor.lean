module
public import SerrePositivity.DifferentialGraded.Tensor.Balanced
public import Mathlib.Data.ZMod.Basic

/-! # 多対象balanced tensorの普遍性の受入検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (M : RightModule A D) (N : LeftModule A D) (T : Complex A) :
    (BalancedTensor.obj A D M N ⟶ T) ≃ BalancedTensor.BalancedFamily A D M N T :=
  BalancedTensor.homEquiv A D M N T
example (M : RightModule (ZMod 2) PUnit.{1}) (N : LeftModule (ZMod 2) PUnit.{1}) :
    Complex (ZMod 2) := BalancedTensor.obj (ZMod 2) PUnit.{1} M N

#print axioms BalancedTensor.rightAction
#print axioms BalancedTensor.leftAction
#print axioms BalancedTensor.rightAction_apply
#print axioms BalancedTensor.leftAction_apply
#print axioms BalancedTensor.objectFamily
#print axioms BalancedTensor.relationFamily
#print axioms BalancedTensor.generators
#print axioms BalancedTensor.relations
#print axioms BalancedTensor.relationLeft
#print axioms BalancedTensor.relationRight
#print axioms BalancedTensor.obj
#print axioms BalancedTensor.projection
#print axioms BalancedTensor.ι
#print axioms BalancedTensor.condition
#print axioms BalancedTensor.BalancedFamily
#print axioms BalancedTensor.desc
#print axioms BalancedTensor.ι_desc
#print axioms BalancedTensor.hom_ext
#print axioms BalancedTensor.homEquiv
#print axioms BalancedTensor.postcompose
#print axioms BalancedTensor.homEquiv_naturality
#print axioms BalancedTensor.desc_postcompose
