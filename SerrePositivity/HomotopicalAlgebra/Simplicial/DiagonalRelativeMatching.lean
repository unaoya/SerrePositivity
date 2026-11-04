module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic

/-!
# 対角の右随伴の相対matching射を実際の境界pullback-Hom射と同型で結ぶ

## 概要
対角の右随伴の相対matching射を実際の境界pullback-Hom射と同型で結ぶ。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
境界matching同型とその値方向の自然性を使う。
二つのpullback標的を同型で結び、それらへ入る相対matching射の一致を確認する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0388][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0388
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Relative matching maps are the actual boundary pullback-Hom maps

The isomorphism compares both pullback targets and the arrows into them.
It uses the proved boundary matching isomorphism and its target naturality.
No model or SM7 assumption is made here.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.BisimplicialModel
variable {Z Y : SSet.{v}} (p : Z ⟶ Y) (n : ℕ)

abbrev boundaryRestriction (T : SSet.{v}) (n : ℕ) :=
  (MonoidalClosed.internalHom.map (SSet.boundary.{v} n).ι.op).app T
abbrev boundaryTargetMap := (ihom (SSet.boundary.{v} n).toSSet).map p
abbrev boundaryPullbackHom : MonoidalClosed.internalHom.PullbackObjObj (SSet.boundary.{v} n).ι p :=
  Functor.PullbackObjObj.ofHasPullback _ _ _

end SerrePositivity.BisimplicialModel
