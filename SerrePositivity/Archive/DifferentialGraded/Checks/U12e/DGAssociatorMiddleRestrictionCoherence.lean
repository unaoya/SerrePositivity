module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionCoherence
public import Mathlib.Data.ZMod.Basic

/-! # 第一中間圏の制限と全導来三因子の結合子coherenceの検査

## 概要
第一中間圏の制限と全導来三因子の結合子coherenceの検査。

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
open CategoryTheory BimoduleTensor
variable (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
  (C : Type w) [DGCategory (ZMod 2) C] [Small.{0} C]
  (D : Type z) [DGCategory (ZMod 2) D] [Small.{0} D]
  (E : Type t) [DGCategory (ZMod 2) E] [Small.{0} E]
  (T : Type s) [DGCategory (ZMod 2) T] [Small.{0} T] (F : DGFunctor (ZMod 2) D C)
  (hE : localHomKFlat (ZMod 2) E) (hT : localHomKFlat (ZMod 2) T)

-- 指定した制限後モデルでの証明。Fは任意、B・C・Dの局所Hom条件は不要。
theorem middleRestrictionAssociatorModel_charTwo
    (Q : RightKFlatBimoduleCategory (ZMod 2) C E)
    (S : RightKFlatBimoduleCategory (ZMod 2) D E)
    (R : RightKFlatBimoduleCategory (ZMod 2) E T)
    (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor (ZMod 2) C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso (ZMod 2) D E q)
    (P : DerivedBimoduleCategory (ZMod 2) B C) :
    (((middleRestrictionAssociatorLeftPath (ZMod 2) B C D E T F hE hT).app
        ((bimoduleToDerived (ZMod 2) E T).obj R.obj)).app
        ((bimoduleToDerived (ZMod 2) C E).obj Q.obj)).app P =
    (((middleRestrictionAssociatorRightPath (ZMod 2) B C D E T F hE hT).app
        ((bimoduleToDerived (ZMod 2) E T).obj R.obj)).app
        ((bimoduleToDerived (ZMod 2) C E).obj Q.obj)).app P := by
  have hm : ((middleRestrictionAssociatorLeftPath (ZMod 2) B C D E T F hE hT).app
        ((bimoduleToDerived (ZMod 2) E T).obj R.obj)).app
        ((bimoduleToDerived (ZMod 2) C E).obj Q.obj) =
      ((middleRestrictionAssociatorRightPath (ZMod 2) B C D E T F hE hT).app
        ((bimoduleToDerived (ZMod 2) E T).obj R.obj)).app
        ((bimoduleToDerived (ZMod 2) C E).obj Q.obj) := by
    rw [middleRestrictionAssociatorLeftPath_app, middleRestrictionAssociatorRightPath_app]
    exact derivedBimoduleAssociator_middleRestriction_model (ZMod 2) B C D E T F hE hT Q R S q hq
  exact NatTrans.congr_app hm P

-- 制限後のK-flat性を仮定せず、全三因子を任意の導来対象にして適用する。
theorem middleRestrictionAssociator_charTwo
    (Q : DerivedBimoduleCategory (ZMod 2) C E) (R : DerivedBimoduleCategory (ZMod 2) E T)
    (P : DerivedBimoduleCategory (ZMod 2) B C) :
    (((middleRestrictionAssociatorLeftPath (ZMod 2) B C D E T F hE hT).app R).app Q).app P =
      (((middleRestrictionAssociatorRightPath (ZMod 2) B C D E T F hE hT).app R).app Q).app P :=
  NatTrans.congr_app
    (NatTrans.congr_app
      (NatTrans.congr_app (middleRestrictionAssociatorPaths_eq (ZMod 2) B C D E T F hE hT) R) Q) P

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded.BimoduleTensor
#check derivedBimoduleAssociator_middleRestriction (ZMod 2)
#print axioms middleRestrictionKFlatFactorIso
#print axioms middleRestrictionKFlatFactorIso_inv
#print axioms middleRestrictionKFlatSourceIso_hom
#print axioms derivedMiddleRestriction_inner_model_square
#print axioms derivedMiddleRestriction_nested_prefix_square
#print axioms derivedMiddleRestriction_nested_model_square
#print axioms derivedMiddleRestriction_pair_model_square
#print axioms derivedBimoduleAssociator_middleRestriction_model
#print axioms derivedBimoduleAssociator_middleRestriction_rightKFlat
#print axioms middleRestrictionAssociatorSource
#print axioms middleRestrictionAssociatorLeftPath
#print axioms middleRestrictionAssociatorRightPath
#print axioms middleRestrictionAssociatorLeftPath_app
#print axioms middleRestrictionAssociatorRightPath_app
#print axioms middleRestrictionAssociatorPaths_eq
#print axioms derivedBimoduleAssociator_middleRestriction

open SerrePositivity.DifferentialGraded.Checks
#print axioms middleRestrictionAssociatorModel_charTwo
#print axioms middleRestrictionAssociator_charTwo
