module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexChainVertices

/-!
# 中断した任意モデル源への一般化：SimplexChainParameter

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual first-vertex parameter of a chain of simplex operators。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0045][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0045
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual first-vertex parameter of a chain of simplex operators

All vertices come from the same first simplex by the actual prefix maps.
Restriction factors through the prefix leading to the new first simplex.
-/
