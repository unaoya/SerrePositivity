module
public import SerrePositivity.DifferentialGraded.Tensor.Yoneda
public import Mathlib.Data.ZMod.Basic

/-! # representable tensorのYoneda評価同型の受入検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (z : D) (N : LeftModule A D) :
    BalancedTensor.obj A D (representable A z) N ≅ N.obj z :=
  BalancedTensor.yonedaIso A D z N
example (N : LeftModule (ZMod 2) PUnit.{1}) :
    BalancedTensor.obj (ZMod 2) PUnit.{1} (representable (ZMod 2) PUnit.unit) N ≅
      N.obj PUnit.unit := BalancedTensor.yonedaIso (ZMod 2) PUnit.{1} PUnit.unit N
example (z : D) (N : LeftModule A D) (x : D)
    (f : GradedHom A x z (-1)) (t : (N.obj x).X 1) :
    (BalancedTensor.yonedaEvaluation A D z N).f 0
      (BalancedTensor.element A D (representable A z) N x f t (by omega)) =
      leftAction A N f t (by omega) :=
  BalancedTensor.yonedaEvaluation_element A D z N x f t (by omega)

#print axioms BalancedTensor.representable_rightAction
#print axioms BalancedTensor.yonedaFamily
#print axioms BalancedTensor.yonedaEvaluation
#print axioms BalancedTensor.ι_yonedaEvaluation
#print axioms BalancedTensor.yonedaEvaluation_element
#print axioms BalancedTensor.yonedaInsertion
#print axioms BalancedTensor.yonedaInsertion_apply
#print axioms BalancedTensor.yonedaInsertion_evaluation
#print axioms BalancedTensor.yonedaEvaluation_insertion
#print axioms BalancedTensor.yonedaIso
