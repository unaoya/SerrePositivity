module
public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import Mathlib.Data.ZMod.Basic

/-! # U11b1：bimoduleの全次数交換則の受入検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]
example (M : Bimodule A B C) (c : C) : RightModule A B := M.rightAt c
example (M : Bimodule A B C) (b : B) : LeftModule A C := M.leftAt b
example (M : Bimodule A B C) {b b' : B} {c c' : C}
    (f : GradedHom A (op b') (op b) (-1)) (g : GradedHom A c c' 1)
    (v : (M.value b' c).X 0) :
    M.actLeft (n := 0) g (M.actRight f v rfl) (by omega) =
      ((1 : ℤ) * -1).negOnePow • M.actRight (n := 0) f (M.actLeft g v rfl) (by omega) :=
  M.act_interchange f g v (by omega)
example (M : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}) (r : ℤ)
    (v : (M.value PUnit.unit PUnit.unit).X r) :
    M.actLeft (unitElement (ZMod 2) PUnit.unit).val v (add_zero r) = v :=
  M.actLeft_unit PUnit.unit PUnit.unit r v

#print axioms Bimodule
#print axioms Bimodule.toFunctor
#print axioms Bimodule.rightAt
#print axioms Bimodule.leftAt
#print axioms Bimodule.value
#print axioms Bimodule.leftCochain
#print axioms Bimodule.interchange
#print axioms Bimodule.leftCochain_eq
#print axioms Bimodule.actRight
#print axioms Bimodule.actLeft
#print axioms Bimodule.act_interchange
#print axioms Bimodule.actRight_unit
#print axioms Bimodule.actLeft_unit
