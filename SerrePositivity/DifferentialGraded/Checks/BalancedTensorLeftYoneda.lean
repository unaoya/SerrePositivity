module
public import SerrePositivity.DifferentialGraded.Tensor.LeftYoneda
public import Mathlib.Data.ZMod.Basic

/-! # 左representable tensorの評価同型と中間次数の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (z : D) (M : RightModule A D) :
    BalancedTensor.obj A D M (leftRepresentable A z) ≅ M.obj (op z) :=
  BalancedTensor.leftYonedaIso A D z M
example (M : RightModule (ZMod 2) PUnit.{1}) :
    BalancedTensor.obj (ZMod 2) PUnit.{1} M (leftRepresentable (ZMod 2) PUnit.unit) ≅
      M.obj (op PUnit.unit) := BalancedTensor.leftYonedaIso (ZMod 2) PUnit.{1} PUnit.unit M
example (z : D) (M : RightModule A D) (x : D)
    (m : (M.obj (op x)).X 1) (f : GradedHom A z x (-1)) :
    (BalancedTensor.leftYonedaEvaluation A D z M).f 0
      (BalancedTensor.element A D M (leftRepresentable A z) x m f (by omega)) =
      (1 * (-1) : ℤ).negOnePow • moduleAction A M f m (by omega) :=
  BalancedTensor.leftYonedaEvaluation_element A D z M x m f (by omega)

#print axioms leftRepresentable
#print axioms leftRepresentable_action
#print axioms associator_apply_of_sums
#print axioms BalancedTensor.leftYonedaFamily
#print axioms BalancedTensor.leftYonedaEvaluation
#print axioms BalancedTensor.ι_leftYonedaEvaluation
#print axioms BalancedTensor.leftYonedaEvaluation_element
#print axioms BalancedTensor.leftYonedaInsertion
#print axioms BalancedTensor.leftYonedaInsertion_apply
#print axioms BalancedTensor.leftYonedaInsertion_evaluation
#print axioms BalancedTensor.leftYonedaEvaluation_insertion
#print axioms BalancedTensor.leftYonedaIso
