module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionPerfectInverse
public import SerrePositivity.DifferentialGraded.Morita.CoherencePerfectAssociator
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalence

/-! # U16：主導来kernel作用・Morita・Perfと係数変更の統合入口

## 概要
受入済みU16a、三条件と明示したcompact生成によるU16c、U16b、および現行U16d比較を公開する。

## 方針
各担当の既存入口を再利用し、共有ルートimportを変更しない。

## 規約と注意
この入口の存在・ビルドはU16全体の受入を意味しない。
U16dの局所化した係数変更関手への正方形接続、U12f成分同定、kernel合成との係数変更図式は未接続。
中心作用も保留。各定理のモデル条件・局所Hom条件・生成性の入力はそのまま保持する。

## 使われ方
U16の最終統合先。受入状態の正本はformalization-plans/dg-theory.md §17と各担当記録。
-/
