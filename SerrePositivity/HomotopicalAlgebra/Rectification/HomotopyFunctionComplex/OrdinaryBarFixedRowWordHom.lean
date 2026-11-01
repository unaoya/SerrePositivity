module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.FreeWordHom
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorCategories
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFixedRowWordHom

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual fixed-outer-degree word Hom augmentation is inverted。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0167][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0167
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual fixed-outer-degree word Hom augmentation is inverted
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed
variable (C : Type u) [Category.{v} C] (N : ℕ) (X Y : D C)

abbrev hom : SSet.{max u v} := FreeWordHom.hom (degree (D C) N) X Y

lemma hom_obj (n : SimplexCategoryᵒᵖ) : (hom C N X Y).obj n =
    ((AmbientWords.sourceFunctor (degree (D C) (N + 1)) (WordSegment.degree.{max u v} n)).obj X ⟶
      (AmbientWords.sourceFunctor (degree (D C) (N + 1)) (WordSegment.degree.{max u v} n)).obj Y) :=
  rfl

def augmentation : hom C N X Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj
    (ULift.{max u v} (FreeGeneratorDegeneracies.hom (N + 1) X Y)) :=
  FreeWordHom.augmentation (degree (D C) N) X Y

lemma augmentation_app (n : SimplexCategoryᵒᵖ) (f : (hom C N X Y).obj n) :
    (augmentation C N X Y).app n f = ULift.up
      ((AmbientWords.augmentation (degree (D C) (N + 1)) (WordSegment.degree.{max u v} n)).map f) :=
  FreeWordHom.augmentation_app (degree (D C) N) X Y n f

lemma map_eq {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (f : (hom C N X Y).obj n) :
    (hom C N X Y).map θ f =
      (AmbientWords.map (𝟭 (degree (D C) (N + 1))) (WordSegment.degreeMap θ)).map f :=
  FreeWordHom.map_eq (degree (D C) N) X Y θ f

lemma localized_augmentation_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (augmentation C N X Y)) :=
  FreeWordHom.localized_augmentation_isIso (degree (D C) N) X Y

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom
