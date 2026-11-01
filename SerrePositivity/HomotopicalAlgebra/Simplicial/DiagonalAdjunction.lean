module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalFrame
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
# 二重単体的集合の対角関手と実際の右随伴の随伴を構成する

## 概要
二重単体的集合の対角関手と実際の右随伴の随伴を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
対角を積添字からの制限として表し、右Kan拡張で右随伴を作る。
関手のcurryingの同値と右Kan拡張の随伴を合成する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0380][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0380
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual diagonal and its ordinary right adjoint

The diagonal is restriction along Delta-op to its square after uncurrying.
Right Kan extension and currying construct its actual right adjoint. No
Quillen compatibility or weak-equivalence preservation is assumed here.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory

namespace SerrePositivity.BisimplicialModel

abbrev currying : (SimplexCategoryᵒᵖ ⥤ SSet.{v}) ≌
    ((SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⥤ Type v) := Functor.currying

abbrev diagonal : (SimplexCategoryᵒᵖ ⥤ SSet.{v}) ⥤ SSet.{v} :=
  currying.functor ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ
    (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) (Type v)).obj (Functor.diag SimplexCategoryᵒᵖ)

abbrev rightAdjoint : SSet.{v} ⥤ SimplexCategoryᵒᵖ ⥤ SSet.{v} :=
  (Functor.diag SimplexCategoryᵒᵖ).ran ⋙ currying.inverse

/- 旧宣言の技術注記：
The genuine adjunction for the actual diagonal restriction.
-/
/-- 二重単体的集合の対角関手と実際の右随伴の随伴を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
対角を積添字からの制限として表し、右Kan拡張で右随伴を作る。
関手のcurryingの同値と右Kan拡張の随伴を合成する。
-/
def diagonalAdjunction : diagonal.{v} ⊣ rightAdjoint.{v} :=
  currying.toAdjunction.comp ((Functor.diag SimplexCategoryᵒᵖ).ranAdjunction (Type v))

instance diagonal_isLeftAdjoint : diagonal.{v}.IsLeftAdjoint :=
  diagonalAdjunction.isLeftAdjoint

instance rightAdjoint_isRightAdjoint : rightAdjoint.{v}.IsRightAdjoint :=
  diagonalAdjunction.isRightAdjoint

@[simp]
lemma diagonal_obj (B : SimplexCategoryᵒᵖ ⥤ SSet.{v}) :
    diagonal.obj B = HomotopyFunctionComplex.DiagonalFrame.obj B := rfl

@[simp]
lemma diagonal_map {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (a : B ⟶ B') :
    diagonal.map a = HomotopyFunctionComplex.DiagonalFrame.map a := rfl

end SerrePositivity.BisimplicialModel
