module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PrependDifferential
public import Mathlib.Data.ZMod.Basic

/-! # 元のHomの追加微分後の作用と符号付きLeibniz則の監査

## 概要
元のHomの追加微分後の作用と符号付きLeibniz則の監査。

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
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGCellAttachment
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

example (x y z : D) :
    homObject A D x y ⊗ C.attachedHom A D I y z ⟶ C.attachedHom A D I x z :=
  C.attachedPrepend A D I x y z

example (x y z : D) (i j n : ℤ) (hn : i + j = n) :
    ιTensorObj (homObject A D x y) (C.attachedHom A D I y z) i j n hn ≫
      (C.attachedPrepend A D I x y z).f n =
    ιTensorObj (homObject A D x y) (C.internalHom A D I y z) i j n hn ≫
      (C.internalPrepend A D I x y z).f n := C.attachedPrepend_ι A D I x y z i j n hn

-- 任意対象宇宙、Dのsmallness・元のHomのflatness・標数制限なし。
example (D : Type v) [DGCategory (ZMod 2) D] (I : Type w) [Small.{0} I]
    (C : Family (ZMod 2) D I) (x y z : D) :
    homObject (ZMod 2) D x y ⊗ C.attachedHom (ZMod 2) D I y z ⟶
      C.attachedHom (ZMod 2) D I x z := C.attachedPrepend (ZMod 2) D I x y z

#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.tensorLeftPathCochain_ext
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_replaceSummand
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_replaceRow
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalPrepend_replacement
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalPrepend_replacement_apply
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalPrepend_total_d_apply
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedPrepend
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedPrepend_ι
