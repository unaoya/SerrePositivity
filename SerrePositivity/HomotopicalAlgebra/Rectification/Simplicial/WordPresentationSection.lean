module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordPresentationAugmentation

/-!
# 中断した任意モデル源への一般化：WordPresentationSection

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The ambient source section of the actual diagonal word augmentation。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0613][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0613
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The ambient source section of the actual diagonal word augmentation

This is the proved ambient inclusion of the presented category. It does not
assert a section of its small-vertex augmentation or any weak equivalence.
-/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.WordPresentationSection
open WordPresentationCat WordPresentationAugmentation

def simplicialSection (C : Cat.{max u v w, u}) : (Functor.const _).obj C ⟶
    (simplicialFunctor.{u, max u v w, w}).obj C where
  app n := (RetractWords.sourceFunctor C (WordSegment.degree.{w} n)).toCatHom
  naturality {_ _} θ := by
    apply Cat.Hom.ext
    change (𝟭 C) ⋙ RetractWords.sourceFunctor C _ =
      RetractWords.sourceFunctor C _ ⋙ RetractWords.map (𝟭 C) (WordSegment.degreeMap θ)
    exact (RetractWords.source_map (𝟭 C) (WordSegment.degreeMap θ)).symm

def simplicialSectionNat : (Functor.const SimplexCategoryᵒᵖ : Cat.{max u v w, u} ⥤ _) ⟶
    simplicialFunctor.{u, max u v w, w} where
  app := simplicialSection.{u, v, w}
  naturality {_ _} F := by
    apply NatTrans.ext
    funext n
    apply Cat.Hom.ext
    change F.toFunctor ⋙ RetractWords.sourceFunctor _ _ =
      RetractWords.sourceFunctor _ _ ⋙
        RetractWords.map F.toFunctor (MonoidWithZeroHom.id (WordSegment.degree.{w} n))
    exact (RetractWords.source_map F.toFunctor (MonoidWithZeroHom.id _)).symm

def diagonalSection (A : SimplicialObject Cat.{max u v w, u}) :
    A ⟶ diagonal.{u, max u v w, w} A :=
  (diagonalConstIso A).inv ≫ CategoryTheory.Functor.whiskerLeft (Functor.diag _)
    (Functor.uncurry.map (CategoryTheory.Functor.whiskerLeft A
      (simplicialSectionNat.{u, v, w})))

lemma diagonalSection_app (A : SimplicialObject Cat.{max u v w, u})
    (n : SimplexCategoryᵒᵖ) : (diagonalSection.{u, v, w} A).app n =
      (RetractWords.sourceFunctor (A.obj n) (WordSegment.degree.{w} n)).toCatHom := by
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

lemma diagonalSection_augmentation (A : SimplicialObject Cat.{max u v w, u}) :
    diagonalSection.{u, v, w} A ≫ diagonalAugmentation.{u, v, w} A = 𝟙 A := by
  apply NatTrans.ext
  funext n
  rw [NatTrans.comp_app, diagonalSection_app]
  apply Cat.Hom.ext
  change RetractWords.sourceFunctor (A.obj n) (WordSegment.degree.{w} n) ⋙
    (RetractWords.augmentation (A.obj n) (WordSegment.degree.{w} n) ⋙ 𝟭 _) = 𝟭 _
  rw [CategoryTheory.Functor.comp_id, RetractWords.source_augmentation]

end SerrePositivity.SimplicialModel.WordPresentationSection
