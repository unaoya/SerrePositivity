module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryNaturality

/-! # 任意位置のcell境界置換と先頭Hom作用の公理監査

## 概要
任意位置のcell境界置換と先頭Hom作用の公理監査。

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

#print axioms SerrePositivity.DifferentialGraded.tensorJoin_action_cochain
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceHead
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceHead_closed
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFirst_eq_head
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_replaceHead
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_replaceFirst
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFace_nil
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFace_zero
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFace_succ
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_tail_hom
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_suffix_hom
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prependMap_replaceFace
