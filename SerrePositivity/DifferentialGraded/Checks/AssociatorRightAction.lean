module
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Components
public import Mathlib.Data.ZMod.Basic

/-! # 両括弧付けの右B作用と符号の検査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

example (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b b' : Bᵒᵖ) (c : C) (e : E) (f : F) (g : GradedHom A b b' (-1))
    (t : (R.value e f).X (-1)) (q : (Q.value c e).X 2) (v : (P.value b.unop c).X 0) :
    moduleAction A ((compose A B E F (compose A B C E P Q) R).rightAt f) g
      (associatorLeftElement A B C E F P Q R b.unop c e f (i := 2) (n := 1)
        t q v (by decide) (by decide)) (show (1 : ℤ) + -1 = 0 by decide) =
    ((-1 : ℤ) * (-1 + 2)).negOnePow •
      associatorLeftElement A B C E F P Q R b'.unop c e f (i := 1) (n := 0) t q
        (moduleAction A (P.rightAt c) (n := -1) g v (by decide)) (by decide) (by decide) :=
  associatorLeft_rightAction_element A B C E F P Q R b b' c e f
    (j := -1) (i' := 1) (by decide) (by decide) (by decide) (by decide) (by decide) g t q v

example (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b b' : Bᵒᵖ) (c : C) (e : E) (f : F) (g : GradedHom A b b' (-1))
    (t : (R.value e f).X (-1)) (q : (Q.value c e).X 2) (v : (P.value b.unop c).X 0) :
    moduleAction A ((compose A B C F P (compose A C E F Q R)).rightAt f) g
      (associatorRightElement A B C E F P Q R b.unop c e f (l := 1) (n := 1)
        t q v (by decide) (by decide)) (show (1 : ℤ) + -1 = 0 by decide) =
    ((-1 : ℤ) * 1).negOnePow •
      associatorRightElement A B C E F P Q R b'.unop c e f (l := 1) (n := 0) t q
        (moduleAction A (P.rightAt c) (n := -1) g v (by decide)) (by decide) (by decide) :=
  associatorRight_rightAction_element A B C E F P Q R b b' c e f
    (j := -1) (by decide) (by decide) (by decide) (by decide) g t q v

example (P Q R : Bimodule (ZMod 2) PUnit.{1} PUnit.{1})
    (b b' : PUnit.{1}ᵒᵖ) (c e f : PUnit.{1}) (g : GradedHom (ZMod 2) b b' (-1))
    (t : (R.value e f).X (-1)) (q : (Q.value c e).X 2) (v : (P.value b.unop c).X 0) :
    moduleAction (ZMod 2)
      ((compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1}
        (compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P Q) R).rightAt f) g
      (associatorLeftElement (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1}
        P Q R b.unop c e f (i := 2) (n := 1) t q v (by decide) (by decide))
      (show (1 : ℤ) + -1 = 0 by decide) =
    ((-1 : ℤ) * (-1 + 2)).negOnePow •
      associatorLeftElement (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1}
        P Q R b'.unop c e f (i := 1) (n := 0) t q
        (moduleAction (ZMod 2) (P.rightAt c) (n := -1) g v (by decide)) (by decide) (by decide) :=
  associatorLeft_rightAction_element (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1}
    P Q R b b' c e f (j := -1) (i' := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) g t q v

#print axioms associatorLeft_rightAction_element
#print axioms associatorRight_rightAction_element
#print axioms associatorValueIso
#print axioms associatorLeftι_hom
