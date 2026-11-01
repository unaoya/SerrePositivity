module
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import Mathlib.Data.ZMod.Basic

/-! # 合成bimoduleの右作用のKoszul符号の検査 -/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

example (P : Bimodule A B C) (Q : Bimodule A C E) (b b' : Bᵒᵖ) (c : C) (e : E)
    (g : GradedHom A b b' (-1)) (q : (Q.value c e).X 1) (v : (P.value b.unop c).X 0) :
    moduleAction A ((compose A B C E P Q).rightAt e) g
      (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b.unop) c q v
        (show (1 : ℤ) + 0 = 1 by decide)) (show (1 : ℤ) + -1 = 0 by decide) =
    ((-1 : ℤ) * 1).negOnePow •
      BalancedTensor.element A C (Q.rightAt e) (P.leftAt b'.unop) c q
        (moduleAction A (P.rightAt c) (n := -1) g v (by decide)) (by decide) :=
  compose_rightAction_element A B C E P Q b b' c e (by decide) (by decide) (by decide) g q v

example (P Q : Bimodule (ZMod 2) PUnit.{1} PUnit.{1})
    (b b' : PUnit.{1}ᵒᵖ) (c e : PUnit.{1})
    (g : GradedHom (ZMod 2) b b' (-1)) (q : (Q.value c e).X 1) (v : (P.value b.unop c).X 0) :
    moduleAction (ZMod 2) ((compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P Q).rightAt e) g
      (BalancedTensor.element (ZMod 2) PUnit.{1} (Q.rightAt e) (P.leftAt b.unop) c q v
        (show (1 : ℤ) + 0 = 1 by decide)) (show (1 : ℤ) + -1 = 0 by decide) =
    ((-1 : ℤ) * 1).negOnePow •
      BalancedTensor.element (ZMod 2) PUnit.{1} (Q.rightAt e) (P.leftAt b'.unop) c q
        (moduleAction (ZMod 2) (P.rightAt c) (n := -1) g v (by decide)) (by decide) :=
  compose_rightAction_element (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P Q b b' c e
    (by decide) (by decide) (by decide) g q v

#print axioms compose_rightAction_element
