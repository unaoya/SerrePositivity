module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import SerrePositivity.HomotopicalAlgebra.Simplicial.GeneratedLeftClass
public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators


/-!
# 境界の左右持ち上げクラスからモデル構造不要のReedy弱因子分解系を構成する

## 概要
境界の左右持ち上げクラスからモデル構造不要のReedy弱因子分解系を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0356][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0356
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual Reedy boundary factorization without a value model structure
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy

namespace SerrePositivity.BisimplicialModel.BoundaryFactorization

lemma boundary_wfs : MorphismProperty.IsWeakFactorizationSystem
    (MorphismProperty.monomorphisms SSet.{v}) SSet.modelCategoryQuillen.I.rlp := by
  let : SSet.modelCategoryQuillen.I.{v}.HasSmallObjectArgument.{v} :=
    SimplicialModel.boundaryGenerators_smallObjectArgument
  have h : MorphismProperty.IsWeakFactorizationSystem SSet.modelCategoryQuillen.I.rlp.llp
      SSet.modelCategoryQuillen.I.rlp :=
    MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp => hi p hp)
  rw [SimplicialModel.boundaryGenerators_leftClass] at h
  exact h

end SerrePositivity.BisimplicialModel.BoundaryFactorization
