module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding

/-!
# 中断した任意モデル源への一般化：OrdinaryBarHomSections

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Split epimorphisms on the Hom augmentations, in every simplicial degree。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0196][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0196
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Split epimorphisms on the Hom augmentations, in every simplicial degree

The sections commute with all simplex operators. They are Hom sections,
not category sections, and supply no strict action on the original base.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarHomSections
open OrdinaryBarFreeResolutionSeed OrdinaryBarDiagonalHomAugmentation
variable (C : Type u) [Category.{v} C] (X Y : D C)

def source : SplitEpi (OrdinaryBarSourceHom.augmentation C X Y) where
  section_ := OrdinaryBarSourceSection.section_ C X Y
  id := OrdinaryBarSourceSection.section_comp_augmentation C X Y

def ambient : SplitEpi (ambientAugmentation C X Y) where
  section_ := (source C X Y).section_ ≫ OrdinaryBarSourceWordEmbedding.ambient C X Y
  id := by
    rw [Category.assoc, OrdinaryBarSourceWordEmbedding.ambient_augmentation]
    exact (source C X Y).id

def small : SplitEpi (smallAugmentation C X Y) where
  section_ := (source C X Y).section_ ≫ OrdinaryBarSourceWordEmbedding.small C X Y
  id := by
    rw [Category.assoc, OrdinaryBarSourceWordEmbedding.small_augmentation]
    exact (source C X Y).id

lemma ambient_surjective (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((ambientAugmentation C X Y).app n) := by
  intro f
  exact ⟨(ambient C X Y).section_.app n f,
    types_congr_hom (congr_app (ambient C X Y).id n) f⟩

lemma small_surjective (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((smallAugmentation C X Y).app n) := by
  intro f
  exact ⟨(small C X Y).section_.app n f,
    types_congr_hom (congr_app (small C X Y).id n) f⟩

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarHomSections
