module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Small.Basic
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SuccPred.Nat
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Lifting
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeArrow
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalRelativeMatching
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.DiagonalRelativeMatching

/-!
# 二重単体的集合の対角はReedy anodyne射をanodyne射へ送る

## 概要
二重単体的集合の対角はReedy anodyne射をanodyne射へ送る。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
対角の右随伴と境界内部Homの比較を使い、相対matching射を計算する。
必要な持ち上げ条件またはBrownの補題を、この実際の比較へ適用する。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0381][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0381
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual diagonal preserves Reedy anodyne maps without a value model structure
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.BisimplicialModel

lemma relativeMatching_horn_rlp {E B : SSet.{v}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) (n : ℕ) :
    SSet.modelCategoryQuillen.J.rlp
      (relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
        (internalHomRight.map p)) := by
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff p).mpr hp
  have : Fibration (boundaryPullbackHom p n).π := SSet.fibration_pullbackObjObjπ _
  have h := (SSet.modelCategoryQuillen.fibration_iff (boundaryPullbackHom p n).π).mp this
  exact (SSet.modelCategoryQuillen.J.rlp.arrow_iso_iff (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.relativeMatchingArrowIso p n)).mpr h

/-- 二重単体的集合の対角はReedy anodyne射をanodyne射へ送る。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
対角の右随伴と境界内部Homの比較を使い、相対matching射を計算する。
必要な持ち上げ条件またはBrownの補題を、この実際の比較へ適用する。
-/
lemma diagonal_map_anodyne {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : A ⟶ B)
    (hf : reedyLeft simplexOp SSet.anodyneExtensions f) :
    SSet.anodyneExtensions (diagonal.map f) := by
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  intro E T p hp
  have : ∀ j : SimplexCategoryᵒᵖ,
      HasLiftingProperty (relativeLatchingMap simplexOp j f)
        (relativeMatchingMap simplexOp j (internalHomRight.map p)) := by
    intro j
    have hr : SSet.modelCategoryQuillen.J.rlp
        (relativeMatchingMap simplexOp j (internalHomRight.map p)) := by
      induction j using Opposite.rec with | _ j =>
        induction j using SimplexCategory.rec with | _ n =>
          exact relativeMatching_horn_rlp p hp n
    exact (hf j) _ hr
  have h : HasLiftingProperty f (internalHomRight.map p) := Lifting.hasLiftingProperty simplexOp
  exact (Adjunction.hasLiftingProperty_iff diagonalInternalHomAdjunction f p).mpr h

lemma localized_diagonal_map_of_reedy_anodyne {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : A ⟶ B)
    (hf : reedyLeft simplexOp SSet.anodyneExtensions f) :
    IsIso (SimplicialModel.AnodyneHomotopy.anodyneQ.map (diagonal.map f)) :=
  Localization.inverts SimplicialModel.AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
    (diagonal_map_anodyne f hf)

end SerrePositivity.BisimplicialModel
