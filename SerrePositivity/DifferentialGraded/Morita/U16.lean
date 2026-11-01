module
public import SerrePositivity.DifferentialGraded.Morita.Adjunction.Coherence



public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalence

/-! # U16：主導来kernel作用・Morita・Perfと係数変更の統合入口

## 概要
受入済みU16a、三条件と明示したcompact生成によるU16c、U16b、および現行U16d比較を公開する。

## 方針
各担当の既存入口を再利用し、共有ルートimportを変更しない。

## 規約と注意
U16全体の受入範囲は、ユーザー決定による各担当の最終受入記録に従う。
U16dの局所化係数変更への正方形は通常代表とhα・hAug・hP'を指定した範囲で接続済み。
二つの変更kernelの合成への作用図式も接続済み。U12f成分同定・合成kernel自体の係数変更比較、
およびその整合性と局所化正方形の全主kernel射自然性は保留。
中心作用と群作用はM9で扱う。各定理のモデル条件・局所Hom条件・生成性の入力はそのまま保持する。

## 使われ方
U16の最終統合先。受入状態の正本は`formalization-plans/dg-theory-m5-status.md`。
-/
