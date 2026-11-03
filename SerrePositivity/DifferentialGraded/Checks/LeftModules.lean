module
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U11a：左dg加群・二重opposite・全次数作用の受入 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

example : LeftModule A D ≃ RightModule A Dᵒᵖ := leftModuleEquivRightOpposite A D
example (M : LeftModule A D) : LeftModule.ofRightOpposite M.toRightOpposite = M := by simp
example (M : LeftModule A D) (x : D) (v : (M.obj x).X (-1)) :
    leftAction A M (unitElement A x).val v (by omega) = v := leftAction_unit A M x (-1) v
example (M : LeftModule A D) {x y z : D} (f : GradedHom A x y (-1))
    (g : GradedHom A y z 1) (v : (M.obj x).X 0) :
    leftAction A M (forward A f g (show (-1 : ℤ) + 1 = 0 by omega)) v (show (0 : ℤ) + 0 = 0 by omega) =
      ((-1 : ℤ) * 1).negOnePow •
        leftAction A M g (leftAction A M f v (show (0 : ℤ) + -1 = -1 by omega)) (show (-1 : ℤ) + 1 = 0 by omega) :=
  leftAction_forward A M (m := 0) (s := -1) (n := 0) f g v (by omega) (by omega) (by omega)
example (M : LeftModule ℤ PUnit.{1}) :
    LeftModule.ofRightOpposite M.toRightOpposite = M := by simp
example (M : LeftModule (ZMod 2) PUnit.{1}) :
    LeftModule.ofRightOpposite M.toRightOpposite = M := by simp

#print axioms doubleOpposite_composition
#print axioms dgDoubleOpposite
#print axioms dgDoubleUnop
#print axioms LeftModule.toRightOpposite
#print axioms LeftModule.ofRightOpposite
#print axioms LeftModule.of_toRightOpposite
#print axioms LeftModule.to_ofRightOpposite
#print axioms leftModuleEquivRightOpposite
#print axioms leftAction
#print axioms leftAction_unit
#print axioms leftAction_forward
