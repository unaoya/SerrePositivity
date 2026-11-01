module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordPresentationSection

/-!
# 中断した任意モデル源への一般化：OrdinaryBarWordResolution

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual augmented bisimplicial word resolution of the ordinary bar base。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0244][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0244
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual augmented bisimplicial word resolution of the ordinary bar base

Both indices are the usual simplex category. All mixed operator identities
come from a functor-valued simplicial object. No model structure is needed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordResolution
open OrdinaryBarFreeResolutionSeed
variable (C : Type u) [Category.{v} C]

abbrev source := OrdinaryBarFreeResolutionNaturalChoice.source (C := C)
abbrev base := FreePathResolutionPresentation.base (D C)

def bisimplicial : SimplicialObject (SimplicialObject Cat.{max u v, u}) :=
  WordPresentationCat.bisimplicial.{u, max u v, max u v} (source C)

def diagonal : SimplicialObject Cat.{max u v, u} :=
  WordPresentationAugmentation.diagonal.{u, max u v, max u v} (source C)

def toFreeResolution : diagonal C ⟶ source C :=
  WordPresentationAugmentation.diagonalAugmentation.{u, max u v, max u v} (source C)

def fromFreeResolution : source C ⟶ diagonal C :=
  WordPresentationSection.diagonalSection.{u, max u v, max u v} (source C)

lemma fromFree_toFree : fromFreeResolution C ≫ toFreeResolution C = 𝟙 (source C) :=
  WordPresentationSection.diagonalSection_augmentation.{u, max u v, max u v} (source C)

def sourceAugmentation : source C ⟶ (Functor.const _).obj (base C) :=
  CategoryTheory.Functor.whiskerLeft SimplexCategory.rev.op
    (FreePathSimplicialResolution.augmentation (D C))

def augmentation : diagonal C ⟶ (Functor.const _).obj (base C) :=
  toFreeResolution C ≫ sourceAugmentation C

lemma fromFree_augmentation : fromFreeResolution C ≫ augmentation C = sourceAugmentation C := by
  rw [augmentation, ← Category.assoc, fromFree_toFree, Category.id_comp]

lemma bisimplicial_obj (n k : SimplexCategoryᵒᵖ) :
    ((bisimplicial C).obj n).obj k =
      Cat.of (RetractWords.Obj ((source C).obj n) (WordSegment.degree.{max u v} k)) := rfl

lemma diagonal_obj (n : SimplexCategoryᵒᵖ) : (diagonal C).obj n =
    Cat.of (RetractWords.Obj ((source C).obj n) (WordSegment.degree.{max u v} n)) := rfl

lemma mixed_naturality {n m k l : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (φ : k ⟶ l) :
    ((bisimplicial C).map θ).app k ≫ ((bisimplicial C).obj m).map φ =
      ((bisimplicial C).obj n).map φ ≫ ((bisimplicial C).map θ).app l :=
  ((bisimplicial C).map θ).naturality φ |>.symm

lemma diagonal_map {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    (diagonal C).map θ =
      ((bisimplicial C).map θ).app n ≫ ((bisimplicial C).obj m).map θ := rfl

lemma augmentation_app (n : SimplexCategoryᵒᵖ) : (augmentation C).app n =
    (RetractWords.augmentation ((source C).obj n) (WordSegment.degree.{max u v} n)).toCatHom ≫
      (sourceAugmentation C).app n := by
  change (_ ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id]
  rfl

lemma augmentation_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    (diagonal C).map θ ≫ (augmentation C).app m = (augmentation C).app n := by
  have h := (augmentation C).naturality θ
  change (diagonal C).map θ ≫ (augmentation C).app m = (augmentation C).app n ≫ 𝟙 _ at h
  exact h.trans (Category.comp_id _)

def projection (n : SimplexCategoryᵒᵖ) : (diagonal C).obj n ⥤ D C :=
  ((augmentation C).app n).toFunctor ⋙ ULiftHom.down.{v, u, u} (C := D C)

lemma projection_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    ((diagonal C).map θ).toFunctor ⋙ projection C m = projection C n := by
  have h := congrArg Cat.Hom.toFunctor (augmentation_naturality C θ)
  change ((diagonal C).map θ).toFunctor ⋙ ((augmentation C).app m).toFunctor =
    ((augmentation C).app n).toFunctor at h
  change (((diagonal C).map θ).toFunctor ⋙ ((augmentation C).app m).toFunctor) ⋙
    ULiftHom.down.{v, u, u} (C := D C) = _
  rw [h]
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordResolution
