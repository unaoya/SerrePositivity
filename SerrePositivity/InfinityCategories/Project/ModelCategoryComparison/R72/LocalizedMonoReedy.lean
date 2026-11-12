module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Small.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SuccPred.Nat
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ClosedObjectwise
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeArrow
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedTransfinite
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestLiftingClass
public import SerrePositivity.HomotopicalAlgebra.Simplicial.LocalizedMonoReedy


/-!
分割で生成：docstring を書き直すこと
# Reedy局所化単射をReedy単射かつ各成分の局所化同値として特徴付ける

## 概要
Reedy局所化単射をReedy単射かつ各成分の局所化同値として特徴付ける。
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
[棚卸し m0448][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0448
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Reedy localized mono equivalences are precisely Reedy monos with localized components
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72

attribute [local instance] _root_.SerrePositivity.SimplicialModel.LocalizedMonoReedy.instIsLocallyPresentableSSet_serrePositivity

/-- Reedy局所化単射をReedy単射かつ各成分の局所化同値として特徴付ける。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma reedy_iff {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : A ⟶ B) :
    reedyLeft simplexOp _root_.SerrePositivity.SimplicialModel.KanTestLiftingClass.localizedMonos f ↔
      reedyLeft simplexOp (MorphismProperty.monomorphisms _) f ∧
        ∀ n, IsIso (_root_.SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map (f.app n)) := by
  have : (MorphismProperty.monomorphisms SSet.{v} ⊓ _root_.SerrePositivity.SimplicialModel.LocalizedMonoReedy.equivalences).IsMultiplicative :=
    _root_.SerrePositivity.SimplicialModel.LocalizedMonoReedy.multiplicative
  have : (MorphismProperty.monomorphisms SSet.{v} ⊓ _root_.SerrePositivity.SimplicialModel.LocalizedMonoReedy.equivalences).IsStableUnderRetracts := _root_.SerrePositivity.SimplicialModel.LocalizedMonoReedy.retracts
  have : (MorphismProperty.monomorphisms SSet.{v} ⊓ _root_.SerrePositivity.SimplicialModel.LocalizedMonoReedy.equivalences).IsStableUnderCoproducts.{v} :=
    _root_.SerrePositivity.SimplicialModel.LocalizedMonoReedy.coproducts
  have : (MorphismProperty.monomorphisms SSet.{v} ⊓ _root_.SerrePositivity.SimplicialModel.LocalizedMonoReedy.equivalences).IsStableUnderCobaseChange :=
    _root_.SerrePositivity.SimplicialModel.LocalizedMonoReedy.cobaseChange
  have : MorphismProperty.IsStableUnderTransfiniteComposition.{v}
      (MorphismProperty.monomorphisms SSet.{v} ⊓ _root_.SerrePositivity.SimplicialModel.LocalizedMonoReedy.equivalences) := _root_.SerrePositivity.SimplicialModel.KanLocalizedTransfinite.stable
  rw [_root_.SerrePositivity.SimplicialModel.LocalizedMonoReedy.localizedMonos_inf]
  exact reedyLeft_inf_iff.{v} simplexOp f (MorphismProperty.monomorphisms _) _root_.SerrePositivity.SimplicialModel.LocalizedMonoReedy.equivalences

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72
