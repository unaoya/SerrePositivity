module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ComonadSimplicialResolution
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionPresentation

/-!
# 中断した任意モデル源への一般化：FreePathSimplicialResolution

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual augmented free-path simplicial resolution of an arbitrary category。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0101][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0101
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual augmented free-path simplicial resolution of an arbitrary category
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.FreePathSimplicialResolution
variable (C : Type u) [Category.{v} C]

def diagram : SimplicialObject Cat.{max u v, u} :=
  ComonadSimplicialResolution.diagram FreePathResolution.comonad
    (FreePathResolutionPresentation.base C)

def augmentation : diagram C ⟶ (Functor.const _).obj (FreePathResolutionPresentation.base C) :=
  ComonadSimplicialResolution.augmentation FreePathResolution.comonad
    (FreePathResolutionPresentation.base C)

def projection (n : SimplexCategoryᵒᵖ) : (diagram C).obj n ⥤ C :=
  ((augmentation C).app n).toFunctor ⋙ ULiftHom.down.{v, u, u} (C := C)

lemma projection_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    ((diagram C).map θ).toFunctor ⋙ projection C m = projection C n := by
  have h := congrArg Cat.Hom.toFunctor ((augmentation C).naturality θ)
  change ((diagram C).map θ).toFunctor ⋙ ((augmentation C).app m).toFunctor =
    ((augmentation C).app n).toFunctor at h
  change (((diagram C).map θ).toFunctor ⋙ ((augmentation C).app m).toFunctor) ⋙
    ULiftHom.down.{v, u, u} (C := C) = _
  rw [h]
  rfl

lemma degree_zero : (diagram C).obj (Opposite.op (SimplexCategory.mk 0)) =
    Cat.of (Paths (ULiftHom.{u} C)) := rfl

lemma degree_one : (diagram C).obj (Opposite.op (SimplexCategory.mk 1)) =
    Cat.of (Paths (Paths (ULiftHom.{u} C))) := rfl

end SerrePositivity.HomotopyFunctionComplex.FreePathSimplicialResolution
