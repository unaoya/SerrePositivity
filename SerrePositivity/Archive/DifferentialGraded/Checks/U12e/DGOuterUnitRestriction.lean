module
public import SerrePositivity.DifferentialGraded.Derived.Paired
public import Mathlib.Data.ZMod.Basic

/-! # 外側制限と単位子：標数2と独立宇宙での検査

## 概要
外側制限と単位子：標数2と独立宇宙での検査。

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
universe v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

-- Fは任意。全導来後因子Qについて、両出力圏の局所Hom条件を明示する。
example (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
    (C : Type w) [DGCategory (ZMod 2) C] [Small.{0} C]
    (D : Type z) [DGCategory (ZMod 2) D] [Small.{0} D]
    (F : DGFunctor (ZMod 2) D C)
    (hC : localHomKFlat (ZMod 2) C) (hD : localHomKFlat (ZMod 2) D)
    (Q : DerivedBimoduleCategory (ZMod 2) B C) :
    (leftUnitOuterLeftRestrictionComparison (ZMod 2) B C D F hC hD).app Q =
      (derivedBimoduleLeftUnitIso (ZMod 2) B D hD).hom.app
        ((derivedBimoduleRestriction (ZMod 2) B D B C (DGFunctor.id B) F).obj Q) := by
  rw [leftUnitOuterLeftRestrictionComparison_eq]
  rfl

-- 通常右単位squareは局所Hom条件・Hom準同型性を要求しない。
example (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
    (D : Type w) [DGCategory (ZMod 2) D] [Small.{0} D]
    (C : Type z) [DGCategory (ZMod 2) C] [Small.{0} C]
    (F : DGFunctor (ZMod 2) D B) (P : BimoduleCategory (ZMod 2) B C) :
    (composeRightRestrictionIso (ZMod 2) B D C C F P
        (BimoduleCategory.of (ZMod 2) C C (Bimodule.diagonal (ZMod 2) C))).hom ≫
      (BimoduleCategory.middleRightRestrictionFunctor (ZMod 2) B D C F).map
        (rightBimoduleUnitIso (ZMod 2) B C
          (BimoduleCategory.underlying (ZMod 2) B C P)).hom =
    (rightBimoduleUnitIso (ZMod 2) D C
      (Bimodule.rightRestriction (ZMod 2) B D C F
        (BimoduleCategory.underlying (ZMod 2) B C P))).hom :=
  rightBimoduleUnitIso_rightRestriction (ZMod 2) B D C F P

#print axioms leftUnitValue_leftRestriction
#print axioms leftBimoduleUnitIso_leftRestriction
#print axioms rightUnitValue_rightRestriction
#print axioms rightBimoduleUnitIso_rightRestriction
#print axioms leftUnitOuterLeftRestrictionComparison
#print axioms leftUnitOuterLeftRestrictionComparison_app
#print axioms leftUnitOuterLeftRestrictionComparison_model
#print axioms leftUnitOuterLeftRestrictionComparison_kFlat
#print axioms leftUnitOuterLeftRestrictionComparison_eq
