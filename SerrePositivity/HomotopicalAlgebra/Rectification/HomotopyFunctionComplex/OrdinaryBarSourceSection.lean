module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSourceContraction

/-!
# 中断した任意モデル源への一般化：OrdinaryBarSourceSection

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A simplicial section on each Hom of the actual source augmentation。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0229][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0229
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A simplicial section on each Hom of the actual source augmentation

This section is on individual Hom simplicial sets. It is not a functorial
section of the category augmentation and asserts no composition law.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceSection
open OrdinaryBarFreeResolutionSeed OrdinaryBarSourceContraction OppositeHomotopy
variable (C : Type u) [Category.{v} C] (X Y : D C)

def section_ : OrdinaryBarDiagonalHomAugmentation.baseHom C X Y ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y) :=
  (baseReverseIso C X Y).inv ≫
    reverseMap (OrdinaryBarSourceExtraDegeneracy.extraDegeneracy C X Y).section_ ≫
      (doubleIso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y))).hom

lemma section_comp_augmentation : section_ C X Y ≫ OrdinaryBarSourceHom.augmentation C X Y =
    𝟙 (OrdinaryBarDiagonalHomAugmentation.baseHom C X Y) := by
  ext n f
  exact types_congr_hom (congr_app
    (OrdinaryBarSourceExtraDegeneracy.extraDegeneracy C X Y).section_comp_hom n) f

lemma augmentation_surjective (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((OrdinaryBarSourceHom.augmentation C X Y).app n) := by
  intro f
  exact ⟨(section_ C X Y).app n f,
    types_congr_hom (congr_app (section_comp_augmentation C X Y) n) f⟩

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceSection
