module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BarConstruction
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor

/-!
# 基底圏上で厳密に関手的な相対barをモデル構造なしで構成する

## 概要
基底圏上で厳密に関手的な相対barをモデル構造なしで構成する。
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
[棚卸し m0522][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0522
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A model-free strict bar candidate on the undecorated base category

For p : D → B and F : D → SSet, use the nerves of degreewise element
categories over p(d) → b. The result is strictly functorial in b. Its
values may lie in the index universe; no smallness or weak equivalence
claim is built into the construction.
-/

@[expose] public section
universe v uD vD uB vB
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})

abbrev elementProjection (n : SimplexCategoryᵒᵖ) : (F.flip.obj n).Elements ⥤ B :=
  Functor.Elements.π (F.flip.obj n) ⋙ p

/-- The two directions of the bar diagram are actual simplicial and base functor maps. -/
def commaLevels : SimplexCategoryᵒᵖ ⥤ B ⥤ Cat.{vD, max uD v vB} where
  obj n := CostructuredArrow.functor (elementProjection p F n)
  map {n m} θ := CostructuredArrow.preFunctor ((F.flip.map θ).mapElements)
    (elementProjection p F m)
  map_id n := by
    rw [F.flip.map_id]
    rfl
  map_comp θ σ := by
    rw [F.flip.map_comp]
    rfl

/- 旧宣言の技術注記：
A strict base functor built by ordinary nerves and the actual bisimplicial diagonal.
-/
/-- 基底圏上で厳密に関手的な相対barをモデル構造なしで構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
abbrev relative : B ⥤ SSet.{max uD vD v vB} :=
  (commaLevels p F).flip ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ Cat.{vD, max uD v vB}
      SSet.{max uD vD v vB}).obj nerveFunctor ⋙
    SerrePositivity.BisimplicialModel.diagonal

lemma relative_obj_degree (b : B) (n : SimplexCategoryᵒᵖ) :
    ((relative p F).obj b).obj n =
      ComposableArrows (CostructuredArrow (elementProjection p F n) b) n.unop.len := rfl

lemma relative_map_degree {b c : B} (f : b ⟶ c) (n : SimplexCategoryᵒᵖ)
    (x : ComposableArrows (CostructuredArrow (elementProjection p F n) b) n.unop.len) :
    ((relative p F).map f).app n x = x ⋙ CostructuredArrow.map f := rfl

end SerrePositivity.SimplicialModel.BarConstruction
