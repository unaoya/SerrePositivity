module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Monad.Basic

public import SerrePositivity.CategoryTheory.Quiver.FreePathComonad

/-!
# 中断した任意モデル源への一般化：FreePathResolution

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The free-path comonad, with explicit generators and all three laws。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0098][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0098
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The free-path comonad, with explicit generators and all three laws

The generic formulas allow independent object and Hom universes. They
provide the counit and duplication operations used in free resolutions;
no model category, enrichment, or infinite-category construction is used.
-/
