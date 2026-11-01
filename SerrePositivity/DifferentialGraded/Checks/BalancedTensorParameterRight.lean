module
public import SerrePositivity.DifferentialGraded.Tensor.Parameter

/-! # 右変数のパラメータ付き作用と主Hom写像の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (M M' : RightModule A D) (N : LeftModule A D) :
    moduleHom A D M M' ⟶ homComplex A (BalancedTensor.obj A D M N)
      (BalancedTensor.obj A D M' N) := BalancedTensor.rightHomMap A D M M' N

#print axioms BalancedTensor.paramRightAction
#print axioms BalancedTensor.rightParamFamily
#print axioms BalancedTensor.rightParamMap
#print axioms BalancedTensor.ι_rightParamMap
#print axioms BalancedTensor.rightParamMap_element
#print axioms BalancedTensor.rightHomMap
#print axioms BalancedTensor.rightHomMap_ι
