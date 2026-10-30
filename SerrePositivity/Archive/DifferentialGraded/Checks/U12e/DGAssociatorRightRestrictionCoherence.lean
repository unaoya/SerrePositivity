module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionCoherence
public import Mathlib.Data.ZMod.Basic

/-! # 全導来結合子と外側右制限の標数2・仮定の検査

## 概要
全導来結合子と外側右制限の標数2・仮定の検査。

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
  (D : Type w) [DGCategory (ZMod 2) D] [Small.{0} D]
  (C : Type z) [DGCategory (ZMod 2) C] [Small.{0} C]
  (E : Type t) [DGCategory (ZMod 2) E] [Small.{0} E]
  (T : Type s) [DGCategory (ZMod 2) T] [Small.{0} T] (F : DGFunctor (ZMod 2) D B)

local notation "RI" => derivedBimoduleRestriction (ZMod 2) D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction (ZMod 2) D T B T F (DGFunctor.id T)

-- 固定後二因子の版には、どの圏にも局所Hom K-flat性を要求しない。
theorem associatorRightRestrictionKFlat_charTwo
    (Q : RightKFlatBimoduleCategory (ZMod 2) C E)
    (R : RightKFlatBimoduleCategory (ZMod 2) E T)
    (P : DerivedBimoduleCategory (ZMod 2) B C) :
    (whiskerLeft RI (rightKFlatDerivedAssociator (ZMod 2) D C E T Q R).hom ≫
      (derivedComposeWithRightRestrictionIso (ZMod 2) B D C T F
        (rightKFlatCompose (ZMod 2) C E T Q R)).hom).app P =
    (whiskerRight (derivedComposeWithRightRestrictionIso (ZMod 2) B D C E F Q).hom
        (rightKFlatDerivedCompose (ZMod 2) D E T R) ≫
      whiskerLeft (rightKFlatDerivedCompose (ZMod 2) B C E Q)
        (derivedComposeWithRightRestrictionIso (ZMod 2) B D E T F R).hom ≫
      whiskerRight (rightKFlatDerivedAssociator (ZMod 2) B C E T Q R).hom RO).app P :=
  NatTrans.congr_app (rightKFlatDerivedAssociator_rightRestriction (ZMod 2) B D C E T F Q R) P

-- 全導来版の条件はE・Tのみ。B・C・Dの局所Hom条件やFの準同値性は追加しない。
theorem associatorRightRestriction_charTwo
    (hE : localHomKFlat (ZMod 2) E) (hT : localHomKFlat (ZMod 2) T)
    (Q : DerivedBimoduleCategory (ZMod 2) C E) (R : DerivedBimoduleCategory (ZMod 2) E T)
    (P : DerivedBimoduleCategory (ZMod 2) B C) :
    (whiskerLeft RI (derivedBimoduleAssociator (ZMod 2) D C E T hE hT Q R).hom ≫
      (derivedBimoduleComposeRightRestrictionIso (ZMod 2) B D C T F hT).hom.app
        (((derivedBimoduleComposeFunctor (ZMod 2) C E T hT).obj R).obj Q)).app P =
    (whiskerRight
        ((derivedBimoduleComposeRightRestrictionIso (ZMod 2) B D C E F hE).hom.app Q)
        ((derivedBimoduleComposeFunctor (ZMod 2) D E T hT).obj R) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor (ZMod 2) B C E hE).obj Q)
        ((derivedBimoduleComposeRightRestrictionIso (ZMod 2) B D E T F hT).hom.app R) ≫
      whiskerRight (derivedBimoduleAssociator (ZMod 2) B C E T hE hT Q R).hom RO).app P :=
  NatTrans.congr_app
    (derivedBimoduleAssociator_rightRestriction (ZMod 2) B D C E T F hE hT Q R) P

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded.BimoduleTensor

#print axioms derivedComposeWithRightRestrictionIso_base_app
#print axioms associatorRightRestriction_localized_square
#print axioms rightRestrictionAssociatorPaths_eq
#print axioms derivedBimoduleAssociator_rightRestriction
#print axioms rightRestrictionAssociatorSource
#print axioms rightRestrictionAssociatorTarget
#print axioms rightRestrictionAssociatorLeftPath
#print axioms rightRestrictionAssociatorRightPath
#print axioms rightRestrictionAssociatorLeftPath_app
#print axioms rightRestrictionAssociatorRightPath_app
#print axioms rightKFlatDerivedAssociator_rightRestriction
#print axioms derivedBimoduleAssociator_rightRestriction_rightKFlat
#print axioms derivedRightRestriction_nested_model_square
#print axioms derivedRightRestriction_pair_model_square
#print axioms rightRestrictionDerivedComposeSourceBaseIso_hom_app
#print axioms rightRestrictionDerivedComposeTargetBaseIso_hom_app
#print axioms derivedBimoduleComposeRightRestrictionIso_model_calculation
#print axioms SerrePositivity.DifferentialGraded.Checks.associatorRightRestrictionKFlat_charTwo
#print axioms SerrePositivity.DifferentialGraded.Checks.associatorRightRestriction_charTwo
