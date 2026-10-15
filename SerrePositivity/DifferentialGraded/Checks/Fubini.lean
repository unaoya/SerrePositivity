module
public import SerrePositivity.DifferentialGraded.Tensor.Fubini
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValues
public import Mathlib.Data.ZMod.Basic

/-! # 相対tensorのFubini同型と左右の普遍性の検査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BalancedTensor
open SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

example (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) :
    leftObj A C E Q R N ≅ rightObj A C E Q R N := Fubini.iso A C E Q R N

example (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) (T : Complex A) :
    (rightObj A C E Q R N ⟶ T) ≃ DoubleFamily A C E Q R N T := rightHomEquiv A C E Q R N T

example (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) (c : C) (e : E) :
    leftι A C E Q R N c e ≫ (Fubini.iso A C E Q R N).hom = rightι A C E Q R N c e :=
  leftι_iso_hom A C E Q R N c e

example (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C)
    (T : Complex A) (f : rightObj A C E Q R N ⟶ T) (c : C) (e : E)
    (t : (R.obj (op e)).X (-1)) (q : (Q.value c e).X 2) (v : (N.obj c).X (-1)) :
    tripleElement A C E (n := 0) (fun c e => rightι A C E Q R N c e ≫ f)
      c e t q v rfl (by decide) =
    familyElement A C (n := 0) (fun c => ι A C (rightModule A C E Q R) N c ≫ f) c
      (element A E R (Q.leftAt c) e t q (show (-1 : ℤ) + 2 = 1 by decide)) v (by decide) :=
  tripleElement_rightι A C E f c e t q v rfl (by decide) (by decide)

example (Q : Bimodule (ZMod 2) PUnit.{1} PUnit.{1})
    (R : RightModule (ZMod 2) PUnit.{1}) (N : LeftModule (ZMod 2) PUnit.{1}) :
    leftObj (ZMod 2) PUnit.{1} PUnit.{1} Q R N ≅
      rightObj (ZMod 2) PUnit.{1} PUnit.{1} Q R N :=
  Fubini.iso (ZMod 2) PUnit.{1} PUnit.{1} Q R N

example (B : Type z) (F : Type t) [DGCategory A B] [DGCategory A F] [Small.{u} B]
    (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F) (b : B) (f : F) :
    (BimoduleTensor.compose A B E F (BimoduleTensor.compose A B C E P Q) R).value b f ≅
      (BimoduleTensor.compose A B C F P (BimoduleTensor.compose A C E F Q R)).value b f :=
  BimoduleTensor.associatorValueIso A B C E F P Q R b f

#print axioms triple_degree_linear_ext
#print axioms paramFamilyMk
#print axioms tripleElement_rightι
#print axioms familyElement_units_smul_left
#print axioms rightι_balanceC
#print axioms inner_element_balanced_of_sum
#print axioms rightι_balanceE
#print axioms rightRestrict
#print axioms rightHomEquiv
#print axioms leftRestrict_row_val
#print axioms rightRestrict_row_val
#print axioms Fubini.iso
#print axioms leftι_iso_hom
#print axioms rightι_iso_inv
#print axioms iso_inv_leftDesc
#print axioms iso_hom_rightDesc
#print axioms BimoduleTensor.compose_leftAt_eq
#print axioms BimoduleTensor.associatorValueIso
