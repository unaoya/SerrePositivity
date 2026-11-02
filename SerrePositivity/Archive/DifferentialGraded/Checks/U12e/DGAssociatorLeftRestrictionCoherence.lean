module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeft
public import Mathlib.Data.ZMod.Basic

/-! # 全三因子に対する外側左制限と導来結合子のcoherenceの検査

## 概要
全三因子に対する外側左制限と導来結合子のcoherenceの検査。

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
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

section CharacteristicTwo
variable (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
  (C : Type w) [DGCategory (ZMod 2) C] [Small.{0} C]
  (E : Type z) [DGCategory (ZMod 2) E] [Small.{0} E]
  (T : Type t) [DGCategory (ZMod 2) T] [Small.{0} T]
  (D : Type s) [DGCategory (ZMod 2) D] [Small.{0} D] (G : DGFunctor (ZMod 2) D T)
  (hE : localHomKFlat (ZMod 2) E) (hT : localHomKFlat (ZMod 2) T)
  (hD : localHomKFlat (ZMod 2) D)
  (Q : DerivedBimoduleCategory (ZMod 2) C E) (R : DerivedBimoduleCategory (ZMod 2) E T)
local notation "LE" => derivedBimoduleRestriction (ZMod 2) E D E T (DGFunctor.id E) G
local notation "L" => derivedBimoduleRestriction (ZMod 2) B D B T (DGFunctor.id B) G

-- Gの準同値性を仮定せず、後二因子も任意の導来対象とする。
theorem SerrePositivity.DifferentialGraded.Checks.associatorLeftRestriction_charTwo_component
    (P : DerivedBimoduleCategory (ZMod 2) B C) :
    ((derivedBimoduleAssociator (ZMod 2) B C E D hE hD Q ((LE).obj R)).hom ≫
      (derivedBimoduleComposeFunctor (ZMod 2) B C D hD).map
        (((derivedBimoduleComposeLeftRestrictionIso (ZMod 2) C E T D G hT hD).inv.app R).app Q) ≫
      (derivedBimoduleComposeLeftRestrictionIso (ZMod 2) B C T D G hT hD).inv.app
        (((derivedBimoduleComposeFunctor (ZMod 2) C E T hT).obj R).obj Q)).app P =
    (whiskerLeft ((derivedBimoduleComposeFunctor (ZMod 2) B C E hE).obj Q)
        ((derivedBimoduleComposeLeftRestrictionIso (ZMod 2) B E T D G hT hD).inv.app R) ≫
      whiskerRight (derivedBimoduleAssociator (ZMod 2) B C E T hE hT Q R).hom L).app P :=
  NatTrans.congr_app
    (derivedBimoduleAssociator_leftRestriction (ZMod 2) B C E T D G hE hT hD Q R) P
end CharacteristicTwo

#check derivedBimoduleAssociator_leftRestriction
#print axioms leftRestrictionAssociatorSource
#print axioms leftRestrictionAssociatorTarget
#print axioms leftRestrictionAssociatorAfterAssociator
#print axioms leftRestrictionAssociatorAfterInner
#print axioms leftRestrictionAssociatorRightMiddle
#print axioms leftRestrictionAssociatorLeftPath
#print axioms leftRestrictionAssociatorRightPath
#print axioms leftRestrictionAssociatorLeftPath_app
#print axioms leftRestrictionAssociatorRightPath_app
#print axioms leftRestrictionAssociatorPaths_eq
#print axioms derivedBimoduleAssociator_leftRestriction
#print axioms
  SerrePositivity.DifferentialGraded.Checks.associatorLeftRestriction_charTwo_component
