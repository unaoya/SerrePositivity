module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorLeftRestriction
public import Mathlib.Data.ZMod.Basic

/-! # 外側左制限と通常結合子のsquareの検査

## 概要
外側左制限と通常結合子のsquareの検査。

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
