module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryOne

public import SerrePositivity.HomotopicalAlgebra.Simplicial.FixedBoundaryExtensions

/-!
# 中断した任意モデル源への一般化：RelativeChoiceSpace

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual spaces of extensions with a fixed simplicial boundary。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0541][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0541
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual spaces of extensions with a fixed simplicial boundary

For a monomorphism i:V→T and a contractible fibrant P, the fiber of
[T,P]→[V,P] at a specified b:V→P is an actual contractible Kan complex.
Its higher parameters are compatible families of extensions, preserving
b in every dimension. No product preservation of a replacement is used.
-/
