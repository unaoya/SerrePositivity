module
public import SerrePositivity.DifferentialGraded.Derived.LeftUnitRestrictionCoherence
public import Mathlib.Data.ZMod.Basic

/-! # 全導来左単位経路と制限後の既存左単位子の一致を検査

## 概要
全導来左単位経路と制限後の既存左単位子の一致を検査。

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

-- Fは任意、局所Hom条件は終端Cだけ。導来対象Qを指定モデルに限定しない。
example (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
    (D : Type w) [DGCategory (ZMod 2) D] [Small.{0} D]
    (C : Type z) [DGCategory (ZMod 2) C] [Small.{0} C]
    (F : DGFunctor (ZMod 2) D B) (hC : localHomKFlat (ZMod 2) C)
    (Q : DerivedBimoduleCategory (ZMod 2) B C) :
    (leftUnitRestrictionDerivedComparison (ZMod 2) B D C F hC).app Q =
      (derivedBimoduleLeftUnitIso (ZMod 2) D C hC).hom.app
        ((derivedBimoduleRestriction (ZMod 2) D C B C F (DGFunctor.id C)).obj Q) := by
  rw [leftUnitRestrictionDerivedComparison_eq]
  rfl

#check leftUnitRestrictionDerivedComparison_model
#check leftUnitRestrictionDerivedComparison_kFlat
#check leftUnitRestrictionDerivedComparison_eq

#print axioms leftUnitRestrictionModelSourceIso_diagonal
#print axioms leftUnitRestrictionDerivedPrefix
#print axioms leftUnitRestrictionDerivedPrefix_model
#print axioms leftUnitRestrictionDerivedComparison_model
#print axioms leftUnitRestrictionDerivedComparison_kFlat
#print axioms leftUnitRestrictionDerivedComparison_eq
