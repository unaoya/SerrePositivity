module
public import SerrePositivity.DifferentialGraded.Tensor.Ring
public import Mathlib.Data.ZMod.Basic

/-! # 一対象環のbalanced tensorと既存非有界tensorの比較検査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]
example (P Q : Complex A) :
    BalancedTensor.obj A PUnit.{1} (ringModule A P) (ringLeftModule A Q) ≅
      SerrePositivity.cochainTensor P Q := BalancedTensor.ringComplexTensorIso A P Q
example (P Q : Complex (ZMod 2)) :
    BalancedTensor.obj (ZMod 2) PUnit.{1} (ringModule (ZMod 2) P) (ringLeftModule (ZMod 2) Q) ≅
      SerrePositivity.cochainTensor P Q := BalancedTensor.ringComplexTensorIso (ZMod 2) P Q

#print axioms ringLeftModule
#print axioms ringLeftModule_map
#print axioms BalancedTensor.ring_rightAction
#print axioms BalancedTensor.ring_leftAction
#print axioms BalancedTensor.ringFamily
#print axioms BalancedTensor.ringIso
#print axioms BalancedTensor.ι_ringIso_hom
#print axioms BalancedTensor.ringIso_hom_element
#print axioms BalancedTensor.ringIso_naturality
#print axioms BalancedTensor.ringComplexTensorIso
