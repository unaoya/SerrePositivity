module
public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import Mathlib.Data.ZMod.Basic

/-! # balanced tensor双関手と斉次成分式の受入検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example : ModuleCategory A D × LeftModuleCategory A D ⥤ Complex A :=
  BalancedTensor.functor A D
example : ModuleCategory (ZMod 2) PUnit.{1} × LeftModuleCategory (ZMod 2) PUnit.{1} ⥤
    Complex (ZMod 2) := BalancedTensor.functor (ZMod 2) PUnit.{1}
example (M : RightModule A D) (N : LeftModule A D) (x y : D)
    (m : (M.obj (op y)).X 1) (f : GradedHom A x y (-1)) (t : (N.obj x).X 0) :
    (1 * (-1) : ℤ).negOnePow • BalancedTensor.element A D M N x (n := 0)
      (moduleAction A M (x := op y) (y := op x) f m rfl) t (by omega) =
    BalancedTensor.element A D M N y m
      (leftAction A N (x := x) (y := y) (n := -1) f t (by omega)) (by omega) :=
  BalancedTensor.element_balanced A D M N x y m f t (n := 0) (by omega)

#print axioms BalancedTensor.rightAction_morphism
#print axioms BalancedTensor.leftAction_morphism
#print axioms BalancedTensor.map
#print axioms BalancedTensor.ι_map
#print axioms BalancedTensor.map_id
#print axioms BalancedTensor.map_comp
#print axioms BalancedTensor.functor
#print axioms BalancedTensor.element
#print axioms BalancedTensor.element_balanced
#print axioms BalancedTensor.map_element
