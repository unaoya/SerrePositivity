module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.Logic.Small.Set

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure

/-!
# 中断した任意モデル源への一般化：SmallParameterClosure

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A small subcomplex closed under a whole simplicial parameter operation。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0574][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0574
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A small subcomplex closed under a whole simplicial parameter operation

Countably many images suffice. Smallness is proved in the original universe
degree by degree; the ambient simplicial set may live in a larger universe.
-/
