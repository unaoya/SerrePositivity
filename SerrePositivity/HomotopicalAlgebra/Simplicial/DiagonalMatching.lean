module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic

/-!
# 対角の右随伴のmatching対象を単体境界への内部Homで表す同型を構成する

## 概要
対角の右随伴のmatching対象を単体境界への内部Homで表す同型を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
標準単体のlatching余極限を境界単体と同定する。
反変内部Homが余極限を極限へ移すことを使い、matching比較を境界への制限と照合する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0386][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0386
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Matching objects of the concrete diagonal right adjoint

The actual latching colimit of standard simplices is the boundary simplex.
Contravariant internal Hom turns this colimit into the actual matching
limit. The comparison formula identifies restriction along the boundary.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.BisimplicialModel

abbrev boundaryHom (Z : SSet.{v}) : SSet.{v}ᵒᵖ ⥤ SSet.{v} :=
  MonoidalClosed.internalHom.flip.obj Z

/- 旧宣言の技術注記：
An actual boundary internal Hom is the actual Reedy matching object.
-/
end SerrePositivity.BisimplicialModel
