module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorLeftRestriction
public import Mathlib.Data.ZMod.Basic

/-! # 外側左制限と通常結合子のsquareの検査 -/
@[expose] public section
noncomputable section
universe v w z t s
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

-- 終端T・Dのsmallnessも局所Hom K-flat性も仮定しない。
example (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
    (C : Type w) [DGCategory (ZMod 2) C] [Small.{0} C]
    (E : Type z) [DGCategory (ZMod 2) E] [Small.{0} E]
    (T : Type t) [DGCategory (ZMod 2) T] (D : Type s) [DGCategory (ZMod 2) D]
    (G : DGFunctor (ZMod 2) D T) (P : BimoduleCategory (ZMod 2) B C)
    (Q : BimoduleCategory (ZMod 2) C E) (R : BimoduleCategory (ZMod 2) E T)
    (b : B) (d : D) :
    (associatorValueIso (ZMod 2) B C E D
      (BimoduleCategory.underlying (ZMod 2) B C P)
      (BimoduleCategory.underlying (ZMod 2) C E Q)
      (BimoduleCategory.underlying (ZMod 2) E D
        ((BimoduleCategory.middleLeftRestrictionFunctor (ZMod 2) E T D G).obj R)) b d).hom =
    (associatorValueIso (ZMod 2) B C E T
      (BimoduleCategory.underlying (ZMod 2) B C P)
      (BimoduleCategory.underlying (ZMod 2) C E Q)
      (BimoduleCategory.underlying (ZMod 2) E T R) b (G.obj d)).hom :=
  associatorValue_leftRestriction (ZMod 2) B C E T D G P Q R b d

#check associatorIso_leftRestriction
#print axioms composeMap_leftRestrictionIso_value
#print axioms associatorValue_leftRestriction
#print axioms associatorIso_leftRestriction
