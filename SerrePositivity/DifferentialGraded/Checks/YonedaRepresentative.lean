module
public import SerrePositivity.DifferentialGraded.Tensor.YonedaRepresentative
public import Mathlib.Data.ZMod.Basic

/-! # dg Yonedaと代表対象を動かす全Hom自然性の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example : DGFunctor A D (RightModule A D) := dgYoneda A D
example : DGFunctor (ZMod 2) PUnit.{1} (RightModule (ZMod 2) PUnit.{1}) :=
  dgYoneda (ZMod 2) PUnit.{1}
example (z z' x : D) (f : GradedHom A (op z) (op z') (-1)) (h : GradedHom A z x 1) :
    (((leftModuleHomπ A D (leftRepresentable A z) (leftRepresentable A z') x).f (-1)
      ((leftYonedaHom A D z z').f (-1) f)).v 1 0 (by omega)) h =
    forward A (D := D) (x := z') (y := z) (z := x) f h (by omega) :=
  leftYonedaHom_element A D z z' x f h (by omega)

#print axioms yonedaHom
#print axioms yonedaHom_π
#print axioms yonedaHom_element
#print axioms yoneda_element_ext
#print axioms yoneda_moduleUnit_π
#print axioms yonedaHom_unit
#print axioms yonedaHom_forward
#print axioms dgYoneda
#print axioms leftYonedaParam
#print axioms leftYonedaHom
#print axioms leftYonedaHom_π
#print axioms leftYonedaHom_element
#print axioms BalancedTensor.yonedaEvaluation_representative_naturality
#print axioms BalancedTensor.leftYonedaEvaluation_representative_naturality
