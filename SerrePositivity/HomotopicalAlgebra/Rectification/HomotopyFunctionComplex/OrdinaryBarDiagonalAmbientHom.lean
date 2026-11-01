module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution
public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.RetractWordIdentities

/-!
# 中断した任意モデル源への一般化：OrdinaryBarDiagonalAmbientHom

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Ambient Hom and its actual small-vertex retract in the diagonal resolution。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0154][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0154
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Ambient Hom and its actual small-vertex retract in the diagonal resolution
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarFixedWordResolution
variable (C : Type u) [Category.{v} C]

abbrev quotientAt (n : SimplexCategoryᵒᵖ) :=
  RetractWords.quotient (degree (D C) (n.unop.len + 1)) (WordSegment.degree.{max u v} n)

abbrev sectionAt (n : SimplexCategoryᵒᵖ) (X : D C) :
    (quotientAt C n).obj (.small X) ⟶ (quotientAt C n).obj (.ambient X) :=
  (quotientAt C n).map (RetractWords.section_ (degree (D C) (n.unop.len + 1))
    (WordSegment.degree.{max u v} n) X)

abbrev projectionAt (n : SimplexCategoryᵒᵖ) (X : D C) :
    (quotientAt C n).obj (.ambient X) ⟶ (quotientAt C n).obj (.small X) :=
  (quotientAt C n).map (RetractWords.projection (degree (D C) (n.unop.len + 1))
    (WordSegment.degree.{max u v} n) X)

abbrev wordAt (n : SimplexCategoryᵒᵖ) (X : D C) (t : WordSegment.degree.{max u v} n) :
    (quotientAt C n).obj (.ambient X) ⟶ (quotientAt C n).obj (.ambient X) :=
  (quotientAt C n).map (RetractWords.word (degree (D C) (n.unop.len + 1))
    (WordSegment.degree.{max u v} n) X t)

lemma map_section {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (X : D C) :
    ((diagram C).map θ).toFunctor.map (sectionAt C n X) = sectionAt C m X := by
  change (RetractWords.map (𝟭 (degree (D C) (m.unop.len + 1)))
    (WordSegment.degreeMap θ)).map
      ((RetractWords.map (OrdinaryBarFixedSource.literalMap C θ)
        (MonoidWithZeroHom.id _)).map (sectionAt C n X)) = _
  dsimp only [sectionAt, quotientAt]
  rw [RetractWords.map_section
    (C := degree (D C) (n.unop.len + 1))
    (OrdinaryBarFixedSource.literalMap C θ) (MonoidWithZeroHom.id _) X]
  exact RetractWords.map_section
    (C := degree (D C) (m.unop.len + 1)) (𝟭 _) (WordSegment.degreeMap θ) X

lemma map_projection {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (X : D C) :
    ((diagram C).map θ).toFunctor.map (projectionAt C n X) = projectionAt C m X := by
  change (RetractWords.map (𝟭 (degree (D C) (m.unop.len + 1)))
    (WordSegment.degreeMap θ)).map
      ((RetractWords.map (OrdinaryBarFixedSource.literalMap C θ)
        (MonoidWithZeroHom.id _)).map (projectionAt C n X)) = _
  dsimp only [projectionAt, quotientAt]
  rw [RetractWords.map_projection
    (C := degree (D C) (n.unop.len + 1))
    (OrdinaryBarFixedSource.literalMap C θ) (MonoidWithZeroHom.id _) X]
  exact RetractWords.map_projection
    (C := degree (D C) (m.unop.len + 1)) (𝟭 _) (WordSegment.degreeMap θ) X

lemma map_word {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (X : D C)
    (t : WordSegment.degree.{max u v} n) :
    ((diagram C).map θ).toFunctor.map (wordAt C n X t) =
      wordAt C m X (WordSegment.degreeMap θ t) := by
  change (RetractWords.map (𝟭 (degree (D C) (m.unop.len + 1)))
    (WordSegment.degreeMap θ)).map
      ((RetractWords.map (OrdinaryBarFixedSource.literalMap C θ)
        (MonoidWithZeroHom.id _)).map (wordAt C n X t)) = _
  dsimp only [wordAt, quotientAt]
  rw [RetractWords.map_word
    (C := degree (D C) (n.unop.len + 1))
    (OrdinaryBarFixedSource.literalMap C θ) (MonoidWithZeroHom.id _) X t]
  exact RetractWords.map_word
    (C := degree (D C) (m.unop.len + 1)) (𝟭 _) (WordSegment.degreeMap θ) X t

def ambientHom (X Y : D C) : SSet.{max u v} where
  obj n := (quotientAt C n).obj (.ambient X) ⟶ (quotientAt C n).obj (.ambient Y)
  map θ := ↾fun f => ((diagram C).map θ).toFunctor.map f
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro f
    have h := congrArg Cat.Hom.toFunctor ((diagram C).map_id n)
    exact congr($(h).map f)
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro f
    have h := congrArg Cat.Hom.toFunctor ((diagram C).map_comp θ φ)
    exact congr($(h).map f)

def transfer (X Y : D C) : ambientHom C X Y ⟶ hom C X Y where
  app n := ↾fun f => sectionAt C n X ≫ f ≫ projectionAt C n Y
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro f
    change sectionAt C m X ≫ ((diagram C).map θ).toFunctor.map f ≫
      projectionAt C m Y =
        ((diagram C).map θ).toFunctor.map (sectionAt C n X ≫ f ≫ projectionAt C n Y)
    rw [Functor.map_comp, Functor.map_comp, map_section, map_projection]

def inclusion (X Y : D C) : hom C X Y ⟶ ambientHom C X Y where
  app n := ↾fun f => projectionAt C n X ≫ f ≫ sectionAt C n Y
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro f
    change projectionAt C m X ≫ ((diagram C).map θ).toFunctor.map f ≫
      sectionAt C m Y =
        ((diagram C).map θ).toFunctor.map (projectionAt C n X ≫ f ≫ sectionAt C n Y)
    rw [Functor.map_comp, Functor.map_comp, map_section, map_projection]

lemma inclusion_transfer (X Y : D C) : inclusion C X Y ≫ transfer C X Y = 𝟙 _ := by
  ext n f
  change sectionAt C n X ≫ (projectionAt C n X ≫ f ≫ sectionAt C n Y) ≫
    projectionAt C n Y = f
  simp only [← Category.assoc, sectionAt, projectionAt, RetractWords.quotient_split,
    Category.id_comp]
  simp only [Category.assoc, RetractWords.quotient_split, Category.comp_id]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom
