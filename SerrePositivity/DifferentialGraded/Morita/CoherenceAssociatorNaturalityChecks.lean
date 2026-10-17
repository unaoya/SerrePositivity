module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociatorRightNaturality

/-! # 主導来kernel結合経路の自然性監査

## 概要
kernel結合子と公開左右経路の最初の二変数の全導来射自然性を監査する。

## 方針
指定代表に限らない自然性の型と公理依存を同じ入口で検証する。

## 規約と注意
任意可換環・独立宇宙を保つ。一般U12e分解変更のcoherenceとは区別する。

## 使われ方
任意kernelへの結合経路の等式の移送を支える検証入口。
-/
@[expose] public section
open SerrePositivity.DifferentialGraded.Morita

#check kernelAssociatorIso_first_naturality
#print axioms kernelAssociatorIso_first_naturality
#check kernelAssociatorIso_second_naturality
#print axioms kernelAssociatorIso_second_naturality
#check kernelAssociatorLeftPath_first_naturality
#print axioms kernelAssociatorLeftPath_first_naturality
#check kernelAssociatorLeftPath_second_naturality
#print axioms kernelAssociatorLeftPath_second_naturality
#check kernelAssociatorRightPath_first_naturality
#print axioms kernelAssociatorRightPath_first_naturality
#check kernelAssociatorRightPath_second_naturality
#print axioms kernelAssociatorRightPath_second_naturality
