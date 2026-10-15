module
public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import Mathlib.Data.ZMod.Basic

/-! # 非有界パラメータ付きbalanced tensorの普遍性の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (M : RightModule A D) (N : LeftModule A D) (K T : Complex A) :
    (K ⊗ BalancedTensor.obj A D M N ⟶ T) ≃ BalancedTensor.ParamFamily A D M N K T :=
  BalancedTensor.paramHomEquiv A D M N K T
example (M : RightModule (ZMod 2) PUnit.{1}) (N : LeftModule (ZMod 2) PUnit.{1})
    (K T : Complex (ZMod 2)) (a : BalancedTensor.ParamFamily (ZMod 2) PUnit.{1} M N K T) :
    K ⟶ homComplex (ZMod 2) (BalancedTensor.obj (ZMod 2) PUnit.{1} M N) T :=
  BalancedTensor.paramHomMap (ZMod 2) PUnit.{1} M N a

#print axioms BalancedTensor.ParamFamily
#print axioms BalancedTensor.curryParamFamily
#print axioms BalancedTensor.paramDesc
#print axioms BalancedTensor.ι_paramDesc
#print axioms BalancedTensor.param_hom_ext
#print axioms BalancedTensor.paramRestrict
#print axioms BalancedTensor.paramHomEquiv
#print axioms BalancedTensor.paramPostcompose
#print axioms BalancedTensor.paramDesc_postcompose
#print axioms BalancedTensor.paramPrecompose
#print axioms BalancedTensor.paramDesc_precompose
#print axioms BalancedTensor.paramHomMap
#print axioms BalancedTensor.paramHomMap_ι
