module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarConstruction

/-!
# 添字変更から相対barの実際の写像を構成する

## 概要
添字変更から相対barの実際の写像を構成する。
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
[棚卸し m0527][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0527
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual relative bar maps induced by reindexing

The two index categories share object and Hom universes; the base and value
universes remain independent. All chains and labels are transported by the
actual functor. No weak equivalence or cofinality assumption is needed.
-/

@[expose] public section
universe v uI vI uB vB
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {E D : Type uI} [Category.{vI} E] [Category.{vI} D]
  {B : Type uB} [Category.{vB} B] (q : E ⥤ D) (p : D ⥤ B) (F : D ⥤ SSet.{v})

abbrev reindexComma (b : B) (n : SimplexCategoryᵒᵖ) :
    CostructuredArrow (elementProjection (q ⋙ p) (q ⋙ F) n) b ⥤
      CostructuredArrow (elementProjection p F n) b :=
  CostructuredArrow.pre (Functor.Elements.precomp q (F.flip.obj n)) (elementProjection p F n) b

def reindexComponent (b : B) : (relative (q ⋙ p) (q ⋙ F)).obj b ⟶ (relative p F).obj b where
  app n := ↾fun c => c ⋙ reindexComma q p F b n
  naturality {_ _} _ := rfl

/- 旧宣言の技術注記：
Reindexing is natural in the original base category before localization.
-/
/-- 添字変更から相対barの実際の写像を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
def reindex : relative (q ⋙ p) (q ⋙ F) ⟶ relative p F where
  app := reindexComponent q p F
  naturality {_ _} _ := rfl

end SerrePositivity.SimplicialModel.BarConstruction
