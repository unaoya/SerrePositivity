module
public import SerrePositivity.DifferentialGraded.Tensor.EnrichedHomPoints
public import Mathlib.Data.ZMod.Basic

/-! # 主Hom複体のtensor–Hom同型とパラメータ普遍性の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

-- 族の転置はDのsmallnessなしで定義できる。
example (K T : Complex A) (M : RightModule A D) (N : LeftModule A D) :
    BalancedTensor.ParamFamily A D M N K T ≃
      ModuleParamTrans A D K M (homRightModule A D N T) :=
  BalancedTensor.paramTransEquiv A D K M N T

example [Small.{u} D] (M : RightModule A D) (N : LeftModule A D) (T : Complex A) :
    homComplex A (BalancedTensor.obj A D M N) T ≅ moduleHom A D M (homRightModule A D N T) :=
  BalancedTensor.enrichedTensorHomIso A D M N T

example [Small.{u} D] (K T : Complex A) (M : RightModule A D) (N : LeftModule A D) :
    (K ⟶ homComplex A (BalancedTensor.obj A D M N) T) ≃
      (K ⟶ moduleHom A D M (homRightModule A D N T)) :=
  BalancedTensor.enrichedTensorHomEquiv A D K M N T

example (M : RightModule (ZMod 2) PUnit.{1}) (N : LeftModule (ZMod 2) PUnit.{1})
    (T : Complex (ZMod 2)) :
    homComplex (ZMod 2) (BalancedTensor.obj (ZMod 2) PUnit.{1} M N) T ≅
      moduleHom (ZMod 2) PUnit.{1} M (homRightModule (ZMod 2) PUnit.{1} N T) :=
  BalancedTensor.enrichedTensorHomIso (ZMod 2) PUnit.{1} M N T

#print axioms BalancedTensor.rightAction_tensorModule
#print axioms BalancedTensor.parameter_balanced_condition_iff
#print axioms BalancedTensor.paramTensorFamily
#print axioms BalancedTensor.tensorParamFamily
#print axioms BalancedTensor.paramTensorFamilyEquiv
#print axioms uncurryRight_precompose
#print axioms curryRight_twice_precompose
#print axioms BalancedTensor.paramTransEquiv
#print axioms BalancedTensor.paramTransEquiv_app
#print axioms BalancedTensor.enrichedTensorHomEquiv
#print axioms BalancedTensor.enrichedTensorHomEquiv_π
#print axioms BalancedTensor.enrichedTensorHomEquiv_naturality_param
#print axioms BalancedTensor.enrichedTensorHomIso
#print axioms BalancedTensor.enrichedTensorHomEquiv_eq_comp
#print axioms BalancedTensor.curryRight_twice_unit
#print axioms BalancedTensor.enrichedTensorHomEquiv_closedMap
