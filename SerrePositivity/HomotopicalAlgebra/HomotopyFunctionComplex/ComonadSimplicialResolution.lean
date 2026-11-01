module

public import SerrePositivity.CategoryTheory.Simplex.PresentationEquivalence
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ComonadResolutionPresentation
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# 任意の余モナドから通常の単体圏上の単体的分解を構成する

## 概要
任意の余モナドから通常の単体圏上の単体的分解を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
余単位と余乗法、または自由な道の生成射を各次数で明示する。
面・退化の関係式と生成射上の一致から、全体の自然性と比較を導く。

## 規約と注意
任意の圏と余モナドを入力し、モデル構造・局所可呈示性は要求しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0077][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0077
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The augmented simplicial resolution of an arbitrary comonad

The index here is the usual simplex category. The comparison with the
presented simplex category is proved in PresentationEquivalence.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.ComonadSimplicialResolution
variable {C : Type u} [Category.{v} C] (G : Comonad C) (X : C)

/-- 任意の余モナドから通常の単体圏上の単体的分解を構成する。

任意の圏と余モナドを入力し、モデル構造・局所可呈示性は要求しない。
余単位と余乗法、または自由な道の生成射を各次数で明示する。
面・退化の関係式と生成射上の一致から、全体の自然性と比較を導く。
-/
def diagram : SimplicialObject C :=
  SimplexPresentation.inverse.op ⋙ ComonadResolutionPresentation.diagram G X

lemma diagram_obj (n : ℕ) :
    (diagram G X).obj (Opposite.op (SimplexCategory.mk n)) =
      ComonadResolutionOperators.power G X (n + 1) := rfl

lemma diagram_face {n : ℕ} (i : Fin (n + 2)) :
    (diagram G X).δ i = ComonadResolutionOperators.face G X (n + 1) i := by
  change (ComonadResolutionPresentation.diagram G X).map
    (SimplexPresentation.inverse.map (SimplexCategory.δ i)).op = _
  rw [SimplexPresentation.inverse_face]
  exact ComonadResolutionPresentation.diagram_face G X i

lemma diagram_degeneracy {n : ℕ} (i : Fin (n + 1)) :
    (diagram G X).σ i = ComonadResolutionOperators.degeneracy G X n i := by
  change (ComonadResolutionPresentation.diagram G X).map
    (SimplexPresentation.inverse.map (SimplexCategory.σ i)).op = _
  rw [SimplexPresentation.inverse_degeneracy]
  exact ComonadResolutionPresentation.diagram_degeneracy G X i

/-- 余モナドの単体的分解から元の対象へのaugmentation自然変換を構成する。

任意の圏と余モナドを入力し、モデル構造・局所可呈示性は要求しない。
余単位と余乗法、または自由な道の生成射を各次数で明示する。
面・退化の関係式と生成射上の一致から、全体の自然性と比較を導く。
-/
def augmentation : diagram G X ⟶ (Functor.const _).obj X :=
  Functor.whiskerLeft SimplexPresentation.inverse.op
    (ComonadResolutionPresentation.augmentationNatTrans G X)

lemma augmentation_app (n : ℕ) :
    (augmentation G X).app (Opposite.op (SimplexCategory.mk n)) =
      ComonadResolutionOperators.augmentation G X (n + 1) := rfl

end SerrePositivity.HomotopyFunctionComplex.ComonadSimplicialResolution
