module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparisonLocalization
public import Mathlib.Data.ZMod.Basic

/-! # 中間dg圏の比較の両因子自然性と前因子の全導来圏への降下の検査

## 概要
中間dg圏の比較の両因子自然性と前因子の全導来圏への降下の検査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)

-- 後端のsmallnessなしで、両因子の実際の閉零射に関して自然。
example {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    composeMap A B D E (BimoduleCategory.middleLeftRestrictionMap A B C D F f)
        (BimoduleCategory.middleRightRestrictionMap A C D E F g) ≫
      middleRestrictionComparisonMap A B C D E F
        (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q') =
    middleRestrictionComparisonMap A B C D E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) ≫
      composeMap A B C E f g := middleRestrictionComparisonMap_naturality A B C D E F f g

example : middleRestrictedComposeFunctor A B C D E F ⟶ composeFunctor A B C E :=
  middleRestrictionComparisonNatTrans A B C D E F

-- 前因子は全導来圏、制限後のK-flat性は仮定しない。
example [Small.{u} E] (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) :
    middleDerivedSourceLift A B C D E F hE Q ⟶
      (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj) :=
  derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q R q hq

example [Small.{u} E] (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) (P : BimoduleCategory A B C) :
    (derivedMiddleRestrictionComparisonFamily A B C D E F hE Q R q hq).app P =
      derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq :=
  derivedMiddleRestrictionComparisonFamily_app A B C D E F hE Q R q hq P

example (X : Type v) (Y : Type w) (Z : Type z) (T : Type t)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [DGCategory (ZMod 2) Z] [DGCategory (ZMod 2) T]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z] (F : DGFunctor (ZMod 2) Z Y) :
    middleRestrictedComposeFunctor (ZMod 2) X Y Z T F ⟶ composeFunctor (ZMod 2) X Y T :=
  middleRestrictionComparisonNatTrans (ZMod 2) X Y Z T F

namespace SerrePositivity.DifferentialGraded
#print axioms BimoduleCategory.middleLeftRestrictionMap
#print axioms BimoduleCategory.middleLeftRestrictionMap_value_eval
#print axioms BimoduleCategory.middleLeftRestrictionFunctor
#print axioms BimoduleCategory.middleRightRestrictionMap_component
#print axioms BimoduleCategory.middleRightRestrictionMap_naturality
#print axioms BimoduleCategory.middleRightRestrictionMap
#print axioms BimoduleCategory.middleRightRestrictionMap_value_eval
#print axioms BimoduleCategory.middleRightRestrictionFunctor
#print axioms BimoduleTensor.middleRestrictionComparisonValue_naturality
#print axioms BimoduleTensor.middleRestrictionComparisonMap_naturality
#print axioms BimoduleTensor.middleRestrictedComposeFunctor
#print axioms BimoduleTensor.middleRestrictionComparisonNatTrans
#print axioms BimoduleTensor.middleRestrictionResolvedMap_naturality
#print axioms BimoduleTensor.middleRestrictionResolvedNatTrans
#print axioms BimoduleTensor.middleDerivedSourceFamily
#print axioms BimoduleTensor.middleDerivedTargetFamily
#print axioms BimoduleTensor.middleDerivedSourceFamilyIso
#print axioms BimoduleTensor.middleDerivedTargetFamilyIso
#print axioms BimoduleTensor.derivedMiddleRestrictionComparisonFamily
#print axioms BimoduleTensor.derivedMiddleRestrictionComparisonFamily_app
#print axioms BimoduleTensor.middleDerivedSourceFamily_inverts
#print axioms BimoduleTensor.middleDerivedSourceLift
#print axioms BimoduleTensor.middleDerivedSourceLift_fac
#print axioms BimoduleTensor.middleDerivedSourceLift_lifting
#print axioms BimoduleTensor.middleDerivedTargetFamily_lifting
#print axioms BimoduleTensor.derivedMiddleRestrictionComparisonLocalized
#print axioms BimoduleTensor.derivedMiddleRestrictionComparisonLocalized_app
end SerrePositivity.DifferentialGraded
