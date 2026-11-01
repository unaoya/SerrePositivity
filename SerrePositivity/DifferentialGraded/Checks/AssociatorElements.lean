module
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Components
public import Mathlib.Data.ZMod.Basic

/-! # 結合比較の斉次元と両括弧付けの左作用の検査 -/
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
    (b : B) (c : C) (e : E) (f : F) (t : (R.value e f).X (-1))
    (q : (Q.value c e).X 2) (v : (P.value b c).X (-1)) :
    (associatorValueIso A B C E F P Q R b f).hom.f 0
      (associatorLeftElement A B C E F P Q R b c e f (i := 1) t q v (by decide) (by decide)) =
    associatorRightElement A B C E F P Q R b c e f (l := 1) (n := 0)
      t q v (by decide) (by decide) :=
  associatorValueIso_hom_element A B C E F P Q R b c e f
    (i := 1) (l := 1) (n := 0)
    t q v (by decide) (by decide) (by decide)

example (P Q R : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}) (b c e f : PUnit.{1})
    (t : (R.value e f).X (-1)) (q : (Q.value c e).X 2) (v : (P.value b c).X (-1)) :
    (associatorValueIso (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R b f).hom.f 0
      (associatorLeftElement (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R b c e f
        (i := 1) t q v (by decide) (by decide)) =
    associatorRightElement (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R b c e f
      (l := 1) (n := 0) t q v (by decide) (by decide) :=
  associatorValueIso_hom_element (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R b c e f
    (i := 1) (l := 1) (n := 0)
    t q v (by decide) (by decide) (by decide)

#print axioms associatorLeftElement
#print axioms associatorRightElement
#print axioms associatorLeftElement_eq_ι
#print axioms associatorRightElement_eq_ι
#print axioms associatorValueIso_hom_element
#print axioms associatorLeft_leftAction_element
#print axioms associatorRight_leftAction_element
#print axioms chain_comp_apply_of_eq

#print axioms chain_ext_apply

#print axioms chain_comp_apply
