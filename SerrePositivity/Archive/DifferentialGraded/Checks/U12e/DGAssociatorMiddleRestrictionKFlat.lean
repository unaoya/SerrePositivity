module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddle

public import Mathlib.Data.ZMod.Basic

/-! # 第一中間圏の指定K-flatモデルと全導来比較の検査

## 概要
第一中間圏の指定K-flatモデルと全導来比較の検査。

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
  (T : Type s) [DGCategory (ZMod 2) T] (F : DGFunctor (ZMod 2) D C)
  (Q : RightKFlatBimoduleCategory (ZMod 2) C E)
  (S : RightKFlatBimoduleCategory (ZMod 2) D E)
  (R : RightKFlatBimoduleCategory (ZMod 2) E T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor (ZMod 2) C D E F).obj Q.obj)

local notation "L" => derivedBimoduleRestriction (ZMod 2) B D B C (DGFunctor.id B) F
local notation "QR" => rightKFlatCompose (ZMod 2) C E T Q R
local notation "SR" => rightKFlatCompose (ZMod 2) D E T S R
local notation "qR" => middleRestrictionComposeAugmentation (ZMod 2) C D E T F Q.obj S.obj R.obj q

-- 局所Hom条件・Tのsmallness・増大の準同型性なし。前因子は任意の導来対象。
theorem associatorMiddleRestrictionKFlat_charTwo (P : DerivedBimoduleCategory (ZMod 2) B C) :
    (whiskerLeft L (rightKFlatDerivedAssociator (ZMod 2) B D E T S R).hom ≫
      rightKFlatMiddleComparison (ZMod 2) B C D T F QR SR qR).app P =
    (whiskerRight (rightKFlatMiddleComparison (ZMod 2) B C D E F Q S q)
        (rightKFlatDerivedCompose (ZMod 2) B E T R) ≫
      (rightKFlatDerivedAssociator (ZMod 2) B C E T Q R).hom).app P :=
  NatTrans.congr_app
    (rightKFlatDerivedAssociator_middleRestriction (ZMod 2) B C D E T F Q S R q) P

-- 実際の全導来比較との一致にはEの局所Hom K-flat性と増大の準同型性を明示する。
theorem middleRestrictionKFlatModel_charTwo (hE : localHomKFlat (ZMod 2) E)
    (hq : BimoduleCategory.quasiIso (ZMod 2) D E q)
    (P : DerivedBimoduleCategory (ZMod 2) B C) :
    ((derivedMiddleRestrictionNatTrans (ZMod 2) B C D E F hE).app
        ((bimoduleToDerived (ZMod 2) C E).obj Q.obj)).app P ≫
      (derivedBimoduleComposeKFlatIso (ZMod 2) B C E hE Q).hom.app P =
    (middleRestrictionKFlatSourceIso (ZMod 2) B C D E F hE Q S q hq).hom.app P ≫
      (rightKFlatMiddleComparison (ZMod 2) B C D E F Q S q).app P :=
  NatTrans.congr_app
    (derivedMiddleRestrictionNatTrans_kFlat_model_calculation (ZMod 2) B C D E F hE Q S q hq) P

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded.BimoduleTensor
#check middleRestrictionInnerAugmentation_model_square (ZMod 2)
#print axioms rightKFlatMiddleSourceBaseIso
#print axioms rightKFlatMiddlePreComparison
#print axioms rightKFlatMiddleComparison
#print axioms rightKFlatMiddleComparison_base_app
#print axioms rightKFlatMiddleComparison_base_square
#print axioms rightKFlatDerivedAssociator_middleRestriction
#print axioms middleRestrictionKFlatSourceIso
#print axioms middleRestrictionKFlatSourceIso_base_calculation
#print axioms derivedMiddleRestrictionNatTrans_kFlat_model_calculation
#print axioms rightKFlatMiddleComposeAugmentation_square
#print axioms middleRestrictionInnerAugmentation_model_square
open SerrePositivity.DifferentialGraded.Checks
#print axioms associatorMiddleRestrictionKFlat_charTwo
#print axioms middleRestrictionKFlatModel_charTwo
