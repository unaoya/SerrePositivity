module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFixedAugmentation

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The augmentation with literal original base objects at every vertex。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0165][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0165
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The augmentation with literal original base objects at every vertex
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed
variable (C : Type u) [Category.{v} C]

def sourceProjection (n : SimplexCategoryᵒᵖ) : degree (D C) (n.unop.len + 1) ⥤ D C where
  obj X := X
  map {X Y} f := eqToHom (OrdinaryBarFixedSource.projection_obj C n X).symm ≫
    (OrdinaryBarFixedSource.projection C n).map f ≫
      eqToHom (OrdinaryBarFixedSource.projection_obj C n Y)
  map_id X := by simp
  map_comp f g := by simp [Category.assoc]

lemma sourceProjection_eq (n : SimplexCategoryᵒᵖ) :
    sourceProjection C n = OrdinaryBarFixedSource.projection C n := by
  refine CategoryTheory.Functor.ext
    (fun X => (OrdinaryBarFixedSource.projection_obj C n X).symm) ?_
  intro X Y f
  simp [sourceProjection]

lemma sourceProjection_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    OrdinaryBarFixedSource.literalMap C θ ⋙ sourceProjection C m = sourceProjection C n := by
  rw [sourceProjection_eq, sourceProjection_eq, OrdinaryBarFixedSource.literalMap_eq]
  exact OrdinaryBarFixedSource.projection_naturality C θ

def projection (n : SimplexCategoryᵒᵖ) :
    (OrdinaryBarFixedWordResolution.diagram C).obj n ⥤ D C :=
  RetractWords.augmentation (degree (D C) (n.unop.len + 1))
    (WordSegment.degree.{max u v} n) ⋙ sourceProjection C n

lemma projection_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    ((OrdinaryBarFixedWordResolution.diagram C).map θ).toFunctor ⋙ projection C m =
      projection C n := by
  change RetractWords.map (OrdinaryBarFixedSource.literalMap C θ)
    (MonoidWithZeroHom.id (WordSegment.degree.{max u v} n)) ⋙
      (RetractWords.map (𝟭 (degree (D C) (m.unop.len + 1))) (WordSegment.degreeMap θ) ⋙
        RetractWords.augmentation (degree (D C) (m.unop.len + 1))
          (WordSegment.degree.{max u v} m)) ⋙ sourceProjection C m = _
  rw [RetractWords.map_augmentation]
  change (RetractWords.map (OrdinaryBarFixedSource.literalMap C θ)
    (MonoidWithZeroHom.id (WordSegment.degree.{max u v} n)) ⋙
      RetractWords.augmentation (degree (D C) (m.unop.len + 1))
        (WordSegment.degree.{max u v} n)) ⋙ sourceProjection C m = _
  rw [RetractWords.map_augmentation]
  change RetractWords.augmentation (degree (D C) (n.unop.len + 1))
    (WordSegment.degree.{max u v} n) ⋙
      (OrdinaryBarFixedSource.literalMap C θ ⋙ sourceProjection C m) = _
  rw [sourceProjection_naturality]
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation
