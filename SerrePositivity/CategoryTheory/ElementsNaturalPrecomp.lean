module

public import Mathlib.CategoryTheory.Elements

/-!
# 自然変換に沿う圏の要素の比較関手を構成する

## 概要
自然変換に沿う圏の要素の比較関手を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
自然変換の成分を使い、要素の圏の対象と射を対応させる。
基底への射影との可換性は元の自然性の式から確認する。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0009][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../formalization-plans/k-theory-generalization-inventory.md#m0009
[plan]: ../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual category-of-elements comparison along a natural transformation

The original elements and all base maps are retained. No faithfulness of
the element projection or smallness of the index category is required.
-/

@[expose] public section
universe vC uC vI uI w
noncomputable section
open CategoryTheory

namespace SerrePositivity.ElementsNaturalPrecomp
variable {C : Type uC} [Category.{vC} C] {I : Type uI} [Category.{vI} I]
  (F : C ⥤ Type w) {P Q : I ⥤ C} (α : P ⟶ Q)

/-- 自然変換に沿う圏の要素の比較関手を構成する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
自然変換の成分を使い、要素の圏の対象と射を対応させる。
基底への射影との可換性は元の自然性の式から確認する。
-/
def comparison : Functor.Elements.precomp P F ⟶
    (Functor.whiskerRight α F).mapElements ⋙ Functor.Elements.precomp Q F where
  app e := Functor.Elements.homMk (α.app e.obj) rfl
  naturality {e e'} f := by
    apply Functor.Elements.hom_ext
    exact α.naturality f.hom

lemma comparison_hom (e : (P ⋙ F).Elements) :
    ((comparison F α).app e).hom = α.app e.obj := rfl

end SerrePositivity.ElementsNaturalPrecomp
