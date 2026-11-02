module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Append.Recursion
public import Mathlib.Data.ZMod.Basic

/-! # 任意次数cellの二重置換相殺と最終Hom微分の監査

## 概要
任意次数cellの二重置換相殺と最終Hom微分の監査。

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
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGCellAttachment
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

-- 任意整数次数・別端点のcell族について、追加微分後の実際の非有界複体を得る。
example (x y : D) : Complex A := C.attachedHom A D I x y

example (x y : D) : homObject A D x y ⟶ C.attachedHom A D I x y :=
  C.originalHomInclusion A D I x y

example (x y : D) (n : ℤ) :
    (C.attachedHom A D I x y).d n (n + 1) ≫
      (C.attachedHom A D I x y).d (n + 1) (n + 1 + 1) = 0 :=
  (C.attachedHom A D I x y).d_comp_d _ _ _

-- DのsmallnessやHomのflatnessを要求せず、標数2にも同じ構成を適用する。
example (D : Type v) [DGCategory (ZMod 2) D] (I : Type w) [Small.{0} I]
    (C : Family (ZMod 2) D I) (x y : D) : Complex (ZMod 2) :=
  C.attachedHom (ZMod 2) D I x y

#print axioms SerrePositivity.DifferentialGraded.tensorJoin_action_cochain
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceHead
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceHead_closed
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFirst_eq_head
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_replaceHead
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_replaceFirst
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFace_nil
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFace_zero
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFace_succ
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_replaceFace
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceHead_face_anticommute
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFirst_face_anticommute
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFace_succ_comp
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.DoubleFace
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.doubleFace
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.negateDoubleFace
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prefixDoubleFace
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prefixDoubleFace_negate
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.doubleFace_cons_succ
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.doubleFace_cons_zero
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.doubleFace_swap_of_le
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.includeDoubleFace
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.includeDoubleFace_negate
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacementPair
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacementPair_swap_of_le
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacementPair_swap
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacementPair_double_sum_zero
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.pathCochain_ext
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacement_square_precomp_double_sum
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacement_square_zero
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedHom
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedHom_X
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.attachedHom_d
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.originalHomInclusion
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.originalHomInclusion_f

#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_tail_hom
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_suffix_hom
