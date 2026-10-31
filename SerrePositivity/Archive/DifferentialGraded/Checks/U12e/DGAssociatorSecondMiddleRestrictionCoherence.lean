module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionCoherence
public import Mathlib.Data.ZMod.Basic

/-! # 第二中間圏の指定モデルと全導来結合子coherenceの検査

## 概要
第二中間圏の指定モデルと全導来結合子coherenceの検査。

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
universe v w z t s
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
  (C : Type w) [DGCategory (ZMod 2) C] [Small.{0} C]
  (D : Type z) [DGCategory (ZMod 2) D] [Small.{0} D]
  (E : Type t) [DGCategory (ZMod 2) E] [Small.{0} E]
  (T : Type s) [DGCategory (ZMod 2) T] (F : DGFunctor (ZMod 2) D E)
  (Q : RightKFlatBimoduleCategory (ZMod 2) C E) (R : RightKFlatBimoduleCategory (ZMod 2) E T)
  (S : RightKFlatBimoduleCategory (ZMod 2) D T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor (ZMod 2) E D T F).obj R.obj)

local notation "LQ" => Functor.obj (rightKFlatLeftRestriction (ZMod 2) C E D F) Q
local notation "QS" => rightKFlatCompose (ZMod 2) C D T LQ S
local notation "QR" => rightKFlatCompose (ZMod 2) C E T Q R
local notation "g" => middleRestrictionResolvedMap (ZMod 2) C E D T F Q.obj R.obj S.obj q

-- 固定モデルではTのsmallness・局所Hom条件・qの準同型性は不要。
theorem secondMiddleRestrictionKFlat_charTwo (P : DerivedBimoduleCategory (ZMod 2) B C) :
    (whiskerRight (derivedComposeWithLeftRestrictionIso (ZMod 2) B C E D F Q).hom
        (rightKFlatDerivedCompose (ZMod 2) B D T S) ≫
      whiskerLeft (rightKFlatDerivedCompose (ZMod 2) B C E Q)
        (rightKFlatMiddleComparison (ZMod 2) B E D T F R S q) ≫
      (rightKFlatDerivedAssociator (ZMod 2) B C E T Q R).hom).app P =
    ((rightKFlatDerivedAssociator (ZMod 2) B C D T LQ S).hom ≫
      rightKFlatDerivedMap (ZMod 2) B C T (Q := QS) (Q' := QR) g).app P :=
  NatTrans.congr_app
    (rightKFlatDerivedAssociator_secondMiddleRestriction (ZMod 2) B C D E T F Q R S q) P

variable [Small.{0} T] (hE : localHomKFlat (ZMod 2) E)
  (hD : localHomKFlat (ZMod 2) D) (hT : localHomKFlat (ZMod 2) T)

-- 指定した制限後モデルを使い、B・Cの局所Hom条件やFの準同値性を要求しない。
theorem secondMiddleRestrictionAssociatorModel_charTwo
    (hq : BimoduleCategory.quasiIso (ZMod 2) D T q)
    (P : DerivedBimoduleCategory (ZMod 2) B C) :
    (((secondMiddleRestrictionAssociatorLeftPath (ZMod 2) B C D E T F hE hD hT).app
        ((bimoduleToDerived (ZMod 2) E T).obj R.obj)).app
        ((bimoduleToDerived (ZMod 2) C E).obj Q.obj)).app P =
    (((secondMiddleRestrictionAssociatorRightPath (ZMod 2) B C D E T F hD hT).app
        ((bimoduleToDerived (ZMod 2) E T).obj R.obj)).app
        ((bimoduleToDerived (ZMod 2) C E).obj Q.obj)).app P := by
  have hm : ((secondMiddleRestrictionAssociatorLeftPath (ZMod 2) B C D E T F hE hD hT).app
        ((bimoduleToDerived (ZMod 2) E T).obj R.obj)).app
        ((bimoduleToDerived (ZMod 2) C E).obj Q.obj) =
      ((secondMiddleRestrictionAssociatorRightPath (ZMod 2) B C D E T F hD hT).app
        ((bimoduleToDerived (ZMod 2) E T).obj R.obj)).app
        ((bimoduleToDerived (ZMod 2) C E).obj Q.obj) := by
    rw [secondMiddleRestrictionAssociatorLeftPath_app,
      secondMiddleRestrictionAssociatorRightPath_app]
    exact derivedBimoduleAssociator_secondMiddleRestriction_model (ZMod 2) B C D E T F
      hE hD hT Q R S q hq
  exact NatTrans.congr_app hm P

-- 制限後のK-flat性を仮定せず、全三因子を任意の導来対象にして適用する。
theorem secondMiddleRestrictionAssociator_charTwo
    (Q' : DerivedBimoduleCategory (ZMod 2) C E) (R' : DerivedBimoduleCategory (ZMod 2) E T)
    (P : DerivedBimoduleCategory (ZMod 2) B C) :
    (((secondMiddleRestrictionAssociatorLeftPath (ZMod 2) B C D E T F hE hD hT).app R').app
        Q').app P =
      (((secondMiddleRestrictionAssociatorRightPath (ZMod 2) B C D E T F hD hT).app R').app
        Q').app P :=
  NatTrans.congr_app
    (NatTrans.congr_app
      (NatTrans.congr_app
        (secondMiddleRestrictionAssociatorPaths_eq (ZMod 2) B C D E T F hE hD hT) R') Q') P

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded.BimoduleTensor
#check derivedBimoduleAssociator_secondMiddleRestriction (ZMod 2)
#print axioms associatorIso_secondMiddleRestriction_resolved
#print axioms rightKFlatDerivedAssociator_secondMiddleRestriction
#print axioms derivedSecondMiddleRestriction_inner_prefix_square
#print axioms derivedSecondMiddleRestriction_inner_model_square
#print axioms derivedSecondMiddleRestriction_nested_model_square
#print axioms derivedSecondMiddleRestriction_pair_comparison_hom
#print axioms derivedSecondMiddleRestriction_pair_model_square
#print axioms derivedBimoduleAssociator_secondMiddleRestriction_model
#print axioms derivedBimoduleAssociator_secondMiddleRestriction_rightKFlat
#print axioms secondMiddleRestrictionAssociatorSource
#print axioms secondMiddleRestrictionAssociatorLeftPath
#print axioms secondMiddleRestrictionAssociatorRightPath
#print axioms secondMiddleRestrictionAssociatorLeftPath_app
#print axioms secondMiddleRestrictionAssociatorRightPath_app
#print axioms secondMiddleRestrictionAssociatorPaths_eq
#print axioms derivedBimoduleAssociator_secondMiddleRestriction

open SerrePositivity.DifferentialGraded.Checks
#print axioms secondMiddleRestrictionKFlat_charTwo
#print axioms secondMiddleRestrictionAssociatorModel_charTwo
#print axioms secondMiddleRestrictionAssociator_charTwo
