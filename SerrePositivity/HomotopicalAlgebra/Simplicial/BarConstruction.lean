module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAdjunction
public import Mathlib.CategoryTheory.Elements
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 添字と値の宇宙を分けたモデル構造不要のbar関手を構成する

## 概要
添字と値の宇宙を分けたモデル構造不要のbar関手を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0347][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0347
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A model-free bar functor with independent index and value universes

Take the nerve of the category of elements at each simplicial degree and
then its bisimplicial diagonal. Values may grow with the index universe.
No model structure is imposed in that larger universe.
-/

@[expose] public section
universe v uD vD
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable (D : Type uD) [Category.{vD} D]

/- 旧宣言の技術注記：
Rows are the actual nerves of categories of degreewise elements.
-/
/-- 図式の各次数の要素の圏のnerveから二重単体的なbarの行を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
abbrev rows : (D ⥤ SSet.{v}) ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{max uD vD v}) :=
  flipFunctor D SimplexCategoryᵒᵖ (Type v) ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ (D ⥤ Type v)
      Cat.{vD, max uD v}).obj Functor.elementsFunctor ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ Cat.{vD, max uD v}
      SSet.{max uD vD v}).obj nerveFunctor

/- 旧宣言の技術注記：
The Bousfield--Kan simplicial replacement, functorial in the whole input diagram.
-/
/-- 添字と値の宇宙を分けたモデル構造不要のbar関手を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
abbrev functor : (D ⥤ SSet.{v}) ⥤ SSet.{max uD vD v} :=
  rows D ⋙ SerrePositivity.BisimplicialModel.diagonal

lemma obj_degree (F : D ⥤ SSet.{v}) (n : SimplexCategoryᵒᵖ) :
    ((functor D).obj F).obj n =
      ComposableArrows ((F.flip.obj n).Elements) n.unop.len := rfl

lemma map_degree {F G : D ⥤ SSet.{v}} (a : F ⟶ G) (n : SimplexCategoryᵒᵖ)
    (c : ComposableArrows ((F.flip.obj n).Elements) n.unop.len) :
    ((functor D).map a).app n c =
      c ⋙ ((Functor.whiskerRight a ((evaluation SimplexCategoryᵒᵖ (Type v)).obj n)).mapElements) :=
  rfl

end SerrePositivity.SimplicialModel.BarConstruction
