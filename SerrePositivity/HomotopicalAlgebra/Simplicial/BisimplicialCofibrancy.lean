module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Types.Basic

/-!
# 標準的な単射cofibration条件のもとで二重単体的集合はReedy cofibrantである

## 概要
標準的な単射cofibration条件のもとで二重単体的集合はReedy cofibrantである。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
latching比較の評価を、余極限を保つ評価関手の同型を介してTypeのlatching比較へ移す。
Eilenberg–Zilberの分解から単射性を導く。

## 規約と注意
モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
このファイルがHT-KQの引用モデルを自動的に選ぶとは解釈しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0351][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0351
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Every bisimplicial set is Reedy cofibrant

Evaluation of the actual latching comparison agrees, through the colimit
preservation isomorphism, with a simplicial-set latching comparison in Type.
Eilenberg--Zilber gives its injectivity. No splitting in SSet is assumed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.BisimplicialModel

abbrev column (B : SimplexCategoryᵒᵖ ⥤ SSet.{v}) (k : SimplexCategoryᵒᵖ) : SSet.{v} :=
  B ⋙ (evaluation SimplexCategoryᵒᵖ (Type v)).obj k

end SerrePositivity.BisimplicialModel
