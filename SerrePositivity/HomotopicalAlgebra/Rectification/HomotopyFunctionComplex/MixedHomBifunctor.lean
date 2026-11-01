module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedDiagonalHomTransport

/-!
# 中断した任意モデル源への一般化：MixedHomBifunctor

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The strict mixed Hom functor on actual pairs of cosimplicial diagrams。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0122][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0122
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The strict mixed Hom functor on actual pairs of cosimplicial diagrams
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory Opposite

namespace SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom
variable {C : Type u} [Category.{v} C]

def functor : (SimplexCategory ⥤ C)ᵒᵖ × (SimplexCategory ⥤ Cᵒᵖ)ᵒᵖ ⥤ SSet.{v} where
  obj X := obj X.1.unop X.2.unop
  map f := map f.1.unop f.2.unop
  map_id X := map_id X.1.unop X.2.unop
  map_comp f g := map_comp f.1.unop g.1.unop f.2.unop g.2.unop

end SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom
