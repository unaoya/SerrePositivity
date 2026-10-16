module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorRightTransport
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorActionDegree
public import SerrePositivity.DifferentialGraded.Bimodule.ActionElement
public import Mathlib.Data.ZMod.Basic

/-! # 値を固定した左作用と結合比較後の作用輸送の受入監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

example (M : Bimodule A B C) (b : B) (c c' : C) (p i n : ℤ)
    (g : GradedHom A c c' p) (v : (M.value b c).X i) (hn : i + p = n) :
    Bimodule.leftActionElement A M g b v hn = leftAction A (M.leftAt b) g v hn :=
  Bimodule.leftActionElement_eq A M g b v hn

example (M : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}) (b c c' : PUnit.{1})
    (g : GradedHom (ZMod 2) c c' (-1)) (v : (M.value b c).X 1) :
    Bimodule.leftActionElement (ZMod 2) M g b v (by decide : 1 + (-1 : ℤ) = 0) =
      leftAction (ZMod 2) (M.leftAt b) g v (by decide) :=
  Bimodule.leftActionElement_eq (ZMod 2) M g b v _

#check BimoduleTensor.associatorRightCochain_transport
#print axioms SerrePositivity.DifferentialGraded.Bimodule.leftActionElement
#print axioms SerrePositivity.DifferentialGraded.Bimodule.leftActionElement_eq
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorRightCochain_transport
#print axioms
  SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValueIso_hom_actionElement_of_degree
#print axioms
  SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValueIso_hom_leftActed_of_degree
