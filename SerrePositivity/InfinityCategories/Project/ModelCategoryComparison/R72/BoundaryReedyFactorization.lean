module
public import Mathlib.AlgebraicTopology.Reedy.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.PEmpty
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Small.Basic
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SuccPred.Nat
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryClasses
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeArrow
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.WeakFactorizationSystem
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryReedyFactorization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.BisimplicialCofibrancy


/-!
分割で生成：docstring を書き直すこと
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

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72

abbrev left : MorphismProperty (SimplexCategoryᵒᵖ ⥤ SSet.{v}) :=
  reedyLeft simplexOp (MorphismProperty.monomorphisms _)
abbrev right : MorphismProperty (SimplexCategoryᵒᵖ ⥤ SSet.{v}) :=
  reedyRight simplexOp SSet.modelCategoryQuillen.I.rlp

/-- 境界の左右持ち上げクラスからモデル構造不要のReedy弱因子分解系を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma reedy_wfs : MorphismProperty.IsWeakFactorizationSystem left.{v} right.{v} := by
  have : MorphismProperty.IsWeakFactorizationSystem
      (MorphismProperty.monomorphisms SSet.{v}) SSet.modelCategoryQuillen.I.rlp := _root_.SerrePositivity.BisimplicialModel.BoundaryFactorization.boundary_wfs
  exact weakFactorizationSystem (C := SSet.{v}) simplexOp
    (MorphismProperty.monomorphisms SSet.{v})
    SSet.modelCategoryQuillen.I.rlp
    (fun _ _ h => Opposite.unop_injective (SimplexCategory.ext h))
    (fun n => ⟨Opposite.op (SimplexCategory.mk n), rfl⟩)

lemma right_app {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (p : A ⟶ B) (hp : right p)
    (j : SimplexCategoryᵒᵖ) : SSet.modelCategoryQuillen.I.rlp (p.app j) := by
  have : MorphismProperty.IsWeakFactorizationSystem
      (MorphismProperty.monomorphisms SSet.{v}) SSet.modelCategoryQuillen.I.rlp := _root_.SerrePositivity.BisimplicialModel.BoundaryFactorization.boundary_wfs
  have hM := matchingEvaluation_mem_right simplexOp j p (MorphismProperty.monomorphisms _)
    SSet.modelCategoryQuillen.I.rlp (fun g => hp g.obj.right)
  have hpb := SSet.modelCategoryQuillen.I.rlp.pullback_fst
    ((matchingComparison simplexOp j).app B) ((matchingEvaluation simplexOp j).map p) hM
  have hc := SSet.modelCategoryQuillen.I.rlp.comp_mem _ _ (hp j) hpb
  exact (relativeMatchingMap_fst simplexOp j p) ▸ hc

lemma right_app_localized {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (p : A ⟶ B) (hp : right p)
    (j : SimplexCategoryᵒᵖ) : IsIso (SimplicialModel.AnodyneHomotopy.anodyneQ.map (p.app j)) := by
  have h := right_app p hp j
  rw [← SSet.rlp_monomorphisms] at h
  exact SimplicialModel.MonoRightLiftingContraction.localized_isIso _ h

lemma left_eq_llp : left.{v} = right.{v}.llp := by
  have : MorphismProperty.IsWeakFactorizationSystem left.{v} right.{v} := reedy_wfs
  exact (MorphismProperty.llp_eq_of_wfs left right).symm

lemma initial_left (A : SimplexCategoryᵒᵖ ⥤ SSet.{v}) : left (initial.to A) := by
  intro j
  have hi : IsIso ((latchingComparison simplexOp j).app
      (⊥_ (SimplexCategoryᵒᵖ ⥤ SSet.{v}))) :=
    isIso_of_isInitial
      (initialIsInitial.isInitialObj (latchingEvaluation simplexOp j) _)
      (initialIsInitial.isInitialObj ((evaluation SimplexCategoryᵒᵖ SSet.{v}).obj j) _) _
  let e : Arrow.mk ((latchingComparison simplexOp j).app A) ≅
      Arrow.mk (relativeLatchingMap simplexOp j (initial.to A)) :=
    Arrow.isoMk (asIso (pushout.inl ((latchingEvaluation simplexOp j).map (initial.to A))
      ((latchingComparison simplexOp j).app (⊥_ (SimplexCategoryᵒᵖ ⥤ SSet.{v})))))
      (Iso.refl _) ((inl_relativeLatchingMap simplexOp j (initial.to A)).trans
        (Category.comp_id _).symm)
  exact ((MorphismProperty.monomorphisms SSet.{v}).arrow_iso_iff e).mp
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.latchingComparison_mono A j)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72
