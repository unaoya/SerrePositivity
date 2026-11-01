module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ComonadResolutionPresentation
public import SerrePositivity.CategoryTheory.Quiver.FreePathComonad
public import Mathlib.CategoryTheory.Category.ULift

/-!
# 自由な道の分解のaugmentationが全次数の単体作用素に関して自然となる

## 概要
自由な道の分解のaugmentationが全次数の単体作用素に関して自然となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
余単位と余乗法、または自由な道の生成射を各次数で明示する。
面・退化の関係式と生成射上の一致から、全体の自然性と比較を導く。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0100][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0100
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The augmented free-path diagram in all degrees, with independent universes

Only Hom is explicitly lifted to place the original category in Cat. The
index is the presented simplex category; its equivalence with the usual
simplex category is not assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.FreePathResolutionPresentation
variable (C : Type u) [Category.{v} C]

abbrev base : Cat.{max u v, u} := Cat.of (ULiftHom.{u} C)

def diagram : SimplexCategoryGenRelᵒᵖ ⥤ Cat.{max u v, u} :=
  ComonadResolutionPresentation.diagram FreePathResolution.comonad (base C)

def augmentation : diagram C ⟶ (Functor.const _).obj (base C) :=
  ComonadResolutionPresentation.augmentationNatTrans FreePathResolution.comonad (base C)

def projection (n : SimplexCategoryGenRelᵒᵖ) : (diagram C).obj n ⥤ C :=
  ((augmentation C).app n).toFunctor ⋙ ULiftHom.down.{v, u, u} (C := C)

/-- 自由な道の分解のaugmentationが全次数の単体作用素に関して自然となる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
余単位と余乗法、または自由な道の生成射を各次数で明示する。
面・退化の関係式と生成射上の一致から、全体の自然性と比較を導く。
-/
lemma projection_naturality {n m : SimplexCategoryGenRelᵒᵖ} (θ : n ⟶ m) :
    ((diagram C).map θ).toFunctor ⋙ projection C m = projection C n := by
  have h := congrArg Cat.Hom.toFunctor ((augmentation C).naturality θ)
  change ((diagram C).map θ).toFunctor ⋙ ((augmentation C).app m).toFunctor =
    ((augmentation C).app n).toFunctor at h
  change (((diagram C).map θ).toFunctor ⋙ ((augmentation C).app m).toFunctor) ⋙
    ULiftHom.down.{v, u, u} (C := C) = _
  rw [h]
  rfl

lemma degree_zero : (diagram C).obj (Opposite.op (SimplexCategoryGenRel.mk 0)) =
    Cat.of (Paths (ULiftHom.{u} C)) := rfl

lemma degree_one : (diagram C).obj (Opposite.op (SimplexCategoryGenRel.mk 1)) =
    Cat.of (Paths (Paths (ULiftHom.{u} C))) := rfl

end SerrePositivity.HomotopyFunctionComplex.FreePathResolutionPresentation
