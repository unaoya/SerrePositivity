module
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import Mathlib.Data.ZMod.Basic

/-! # U12eの相対K-flat合成と指定準同型保存の受入監査

## 概要
U12eの相対K-flat合成と指定準同型保存の受入監査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B]

example : Bimodule.rightRelativeKFlat A B B (Bimodule.diagonal A B) :=
  Bimodule.diagonal_rightRelativeKFlat A B

example : (BimoduleCategory.quasiIso A B C).HasTwoOutOfThreeProperty := inferInstance
example : (BimoduleCategory.quasiIso A B C).IsStableUnderRetracts := inferInstance

example (P : Bimodule A B C)
    (h : ∀ c, moduleSemifree A B (ForgetEnrichment.of (Complex A) (P.rightAt c))) :
    Bimodule.rightRelativeKFlat A B C P :=
  Bimodule.rightRelativeKFlat_of_rightAt_semifree A B C P h

variable [Small.{u} C]
-- Eのsmall性やHomのA-flat性は、以下の合成閉性の追加仮定ではない。
example (P : Bimodule A B C) (Q : Bimodule A C E)
    (hP : Bimodule.rightRelativeKFlat A B C P)
    (hQ : Bimodule.rightRelativeKFlat A C E Q) :
    Bimodule.rightRelativeKFlat A B E (compose A B C E P Q) :=
  Bimodule.rightRelativeKFlat_compose A B C E P Q hP hQ

example {P P' : BimoduleCategory A B C} (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (f : P ⟶ P') (hf : BimoduleCategory.quasiIso A B C f) :
    BimoduleCategory.quasiIso A B E (composeMap A B C E f (𝟙 Q)) :=
  composeMap_first_quasiIso A B C E Q hQ f hf

example {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (hQ : ∀ e, moduleHomotopicallyProjective A C
      ((BimoduleCategory.evaluation A C E e).obj Q))
    (hQ' : ∀ e, moduleHomotopicallyProjective A C
      ((BimoduleCategory.evaluation A C E e).obj Q'))
    (f : P ⟶ P') (g : Q ⟶ Q')
    (hf : BimoduleCategory.quasiIso A B C f) (hg : BimoduleCategory.quasiIso A C E g) :
    BimoduleCategory.quasiIso A B E (composeMap A B C E f g) :=
  composeMap_projective_quasiIso A B C E hQ hQ' f g hf hg

example : Bimodule.rightRelativeKFlat (ZMod 2) PUnit.{1} PUnit.{1}
    (Bimodule.diagonal (ZMod 2) PUnit.{1}) :=
  Bimodule.diagonal_rightRelativeKFlat (ZMod 2) PUnit.{1}

#print axioms SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat
#print axioms SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_of_iso
#print axioms SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_of_retract
#print axioms SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_of_rightAt_semifree
#print axioms SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_of_rightAt_projective
#print axioms SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat
#print axioms SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso_iff
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso_eq_iInf
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIsoIsMultiplicative
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIsoHasTwoOutOfThree
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIsoStableUnderRetracts
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIsoRespectsIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso_evaluation
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso_leftEvaluation
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap_first_quasiIso
#print axioms
      SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap_second_projective_quasiIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap_projective_quasiIso
