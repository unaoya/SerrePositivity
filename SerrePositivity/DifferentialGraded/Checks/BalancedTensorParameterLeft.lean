module
public import SerrePositivity.DifferentialGraded.Tensor.ParameterLeft
public import Mathlib.Data.ZMod.Basic

/-! # 左変数のパラメータ作用・Koszul符号・主Hom写像の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Opposite HomologicalComplex SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (M : RightModule A D) (N N' : LeftModule A D) :
    leftModuleHom A D N N' ⟶ homComplex A (BalancedTensor.obj A D M N)
      (BalancedTensor.obj A D M N') := BalancedTensor.leftHomMap A D M N N'
example (M : RightModule (ZMod 2) PUnit.{1}) (N N' : LeftModule (ZMod 2) PUnit.{1}) :
    leftModuleHom (ZMod 2) PUnit.{1} N N' ⟶
      homComplex (ZMod 2) (BalancedTensor.obj (ZMod 2) PUnit.{1} M N)
        (BalancedTensor.obj (ZMod 2) PUnit.{1} M N') :=
  BalancedTensor.leftHomMap (ZMod 2) PUnit.{1} M N N'
example (M : RightModule A D) (N N' : LeftModule A D) (x : D)
    (τ : (leftModuleHom A D N N').X (-1)) (m : (M.obj (op x)).X 1) (v : (N.obj x).X 0) :
    (BalancedTensor.leftParamMap A D M (leftModuleHomπ A D N N')
      (leftModuleHomπ_naturality A D N N')).f 0
      (ιTensorObj (leftModuleHom A D N N') (BalancedTensor.obj A D M N) (-1) (1 + 0) 0
        (by omega) (τ ⊗ₜ[A] BalancedTensor.element A D M N x m v rfl)) =
    ((-1) * 1 : ℤ).negOnePow • BalancedTensor.element A D M N' x m
      (((leftModuleHomπ A D N N' x).f (-1) τ).v 0 (-1 + 0) (by omega) v) (by omega) :=
  BalancedTensor.leftParamMap_element A D M (leftModuleHomπ A D N N')
    (leftModuleHomπ_naturality A D N N') x τ m v (by omega)

#print axioms leftParamNaturality_apply_of_sum
#print axioms leftModuleHomπ_naturality
#print axioms parameterCross
#print axioms parameterCross_naturality_left
#print axioms parameterCross_naturality_right
#print axioms parameterCross_tensor
#print axioms parameterCross_apply
#print axioms BalancedTensor.paramLeftAction
#print axioms BalancedTensor.leftParamFamily
#print axioms BalancedTensor.leftParamMap
#print axioms BalancedTensor.ι_leftParamMap
#print axioms BalancedTensor.leftParamMap_element
#print axioms BalancedTensor.leftHomMap
#print axioms BalancedTensor.leftHomMap_ι
