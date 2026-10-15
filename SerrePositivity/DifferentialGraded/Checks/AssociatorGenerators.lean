module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorCochainExt
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleElements
public import Mathlib.Data.ZMod.Basic

/-! # 結合比較の三重生成元と全次数作用の検査 -/
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
    (b : B) (c : C) (e : E) (f : F) :
    associatorLeftι A B C E F P Q R b c e f ≫ (associatorValueIso A B C E F P Q R b f).hom =
      associatorRightι A B C E F P Q R b c e f := associatorLeftι_hom A B C E F P Q R b c e f

example (P : Bimodule A B C) (Q : Bimodule A C E) (b : B) (c : C) (e e' : E)
    (g : GradedHom A e e' (-1)) (q : (Q.value c e).X 2) (v : (P.value b c).X 0) :
    leftAction A ((compose A B C E P Q).leftAt b) g
      (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v (show (2 : ℤ) + 0 = 2 by decide))
      (show (2 : ℤ) + -1 = 1 by decide) =
    BalancedTensor.element A C (Q.rightAt e') (P.leftAt b) c
      (leftAction A (Q.leftAt c) (n := 1) g q (by decide)) v (by decide) :=
  compose_leftAction_element A B C E P Q b c e e' (by decide) (by decide) (by decide) g q v

example (P Q R : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}) (b c e f : PUnit.{1}) :
    associatorLeftι (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R b c e f ≫
      (associatorValueIso (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R b f).hom =
    associatorRightι (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R b c e f :=
  associatorLeftι_hom (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R b c e f

#print axioms associatorLeftι
#print axioms associatorRightι
#print axioms associatorLeftι_transport
#print axioms associatorLeftι_hom
#print axioms associatorRightι_inv
#print axioms associatorLeft_hom_ext
#print axioms associatorRight_hom_ext
#print axioms associatorLeft_cochain_element_ext
#print axioms compose_leftAction_element
