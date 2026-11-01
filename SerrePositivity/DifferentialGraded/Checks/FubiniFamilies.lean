module
public import SerrePositivity.DifferentialGraded.Tensor.Fubini

public import Mathlib.Data.ZMod.Basic

/-! # 二重balanced族の左反復coend普遍性と右作用の検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BalancedTensor
open SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

example (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) (T : Complex A) :
    (leftObj A C E Q R N ⟶ T) ≃ DoubleFamily A C E Q R N T := leftHomEquiv A C E Q R N T

example (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C)
    (T : Complex A) (f : leftObj A C E Q R N ⟶ T) (c : C) (e : E)
    (t : (R.obj (op e)).X (-1)) (q : (Q.value c e).X 2) (v : (N.obj c).X (-1)) :
    tripleElement A C E (n := 0) (fun c e => leftι A C E Q R N c e ≫ f) c e t q v rfl (by decide) =
      familyElement A E (n := 0) (fun e => ι A E R (leftModule A C E Q N) e ≫ f) e t
        (element A C (Q.rightAt e) N c q v rfl) (by decide) :=
  tripleElement_leftι A C E f c e t q v rfl (by decide)

example (Q : Bimodule (ZMod 2) PUnit.{1} PUnit.{1})
    (R : RightModule (ZMod 2) PUnit.{1}) (N : LeftModule (ZMod 2) PUnit.{1})
    (T : Complex (ZMod 2)) :
    (leftObj (ZMod 2) PUnit.{1} PUnit.{1} Q R N ⟶ T) ≃
      DoubleFamily (ZMod 2) PUnit.{1} PUnit.{1} Q R N T :=
  leftHomEquiv (ZMod 2) PUnit.{1} PUnit.{1} Q R N T

#print axioms leftModule
#print axioms rightModule
#print axioms leftObj
#print axioms rightObj
#print axioms leftι
#print axioms rightι
#print axioms left_hom_ext
#print axioms right_hom_ext
#print axioms leftModule_action_element
#print axioms TripleFamily
#print axioms tripleElement
#print axioms DoubleFamily
#print axioms rowCurry_balanceE
#print axioms leftFamily
#print axioms leftDesc
#print axioms leftι_leftDesc
#print axioms tripleElement_leftι
#print axioms familyElement_inner_reindex
#print axioms leftRestrict
#print axioms leftHomEquiv
#print axioms rightModule_action_element
