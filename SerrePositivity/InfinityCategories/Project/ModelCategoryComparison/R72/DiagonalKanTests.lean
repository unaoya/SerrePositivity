module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
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
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Small.Basic
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SuccPred.Nat
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Lifting
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeArrow
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAdjunction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAnodyne
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalInternalHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalKanTests
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalRelativeMatching
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedMonoLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestLiftingClass
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.DiagonalRelativeMatching


/-!
分割で生成：docstring を書き直すこと
# Reedy局所化単射の対角がanodyne局所化で可逆となることをKan値テストから導く

## 概要
Reedy局所化単射の対角がanodyne局所化で可逆となることをKan値テストから導く。
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
[棚卸し m0384][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0384
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The diagonal inverts Reedy localized mono equivalences by actual Kan tests
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.SimplicialModel
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72

lemma relativeMatching_target_kan {E B : SSet.{v}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p)
    (hB : SSet.modelCategoryQuillen.J.rlp (terminal.from B)) (n : ℕ) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from
      (pullback (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.reedyRestriction B n) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.reedyTargetMap p n))) := by
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff _).mpr hp
  have : Fibration (terminal.from B) := (SSet.modelCategoryQuillen.fibration_iff _).mpr hB
  have : SSet.KanComplex B := (isFibrant_iff B).mpr inferInstance
  have ht : Fibration (_root_.SerrePositivity.BisimplicialModel.boundaryTargetMap p n) :=
    inferInstanceAs (Fibration ((ihom (SSet.boundary n).toSSet).map p))
  have hpb := (SSet.modelCategoryQuillen.J.rlp).pullback_snd
    (_root_.SerrePositivity.BisimplicialModel.boundaryTargetMap p n) (_root_.SerrePositivity.BisimplicialModel.boundaryRestriction B n)
    ((SSet.modelCategoryQuillen.fibration_iff _).mp ht)
  have : Fibration (pullback.snd (_root_.SerrePositivity.BisimplicialModel.boundaryTargetMap p n) (_root_.SerrePositivity.BisimplicialModel.boundaryRestriction B n)) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr hpb
  have hKan : IsFibrant ((ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj B) :=
    inferInstance
  have : IsFibrant (_root_.SerrePositivity.BisimplicialModel.boundaryPullbackHom p n).pt :=
    isFibrant_of_fibration (pullback.snd (_root_.SerrePositivity.BisimplicialModel.boundaryTargetMap p n) (_root_.SerrePositivity.BisimplicialModel.boundaryRestriction B n))
      (hY := hKan)
  have : IsFibrant (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.relativeTarget p n) := isFibrant_of_fibration (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.relativeTargetIso p n).hom
  exact (SSet.modelCategoryQuillen.fibration_iff _).mp this

lemma diagonal_lifting_of_reedy_localizedMonos {A T : SimplexCategoryᵒᵖ ⥤ SSet.{v}}
    (i : A ⟶ T) (hi : reedyLeft simplexOp KanTestLiftingClass.localizedMonos i)
    {E B : SSet.{v}} (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
    (hB : SSet.modelCategoryQuillen.J.rlp (terminal.from B)) :
    HasLiftingProperty (_root_.SerrePositivity.BisimplicialModel.diagonal.map i) p := by
  have : ∀ j : SimplexCategoryᵒᵖ,
      HasLiftingProperty (relativeLatchingMap simplexOp j i)
        (relativeMatchingMap simplexOp j (_root_.SerrePositivity.BisimplicialModel.internalHomRight.map p)) := by
    intro j
    have : Mono (relativeLatchingMap simplexOp j i) := (hi j).1
    induction j using Opposite.rec with | _ j =>
      induction j using SimplexCategory.rec with | _ n =>
        exact KanLocalizedMonoLifting.hasLiftingProperty _ (hi _).2 _
          (_root_.SerrePositivity.BisimplicialModel.relativeMatching_horn_rlp p hp n) (relativeMatching_target_kan p hp hB n)
  have h : HasLiftingProperty i (_root_.SerrePositivity.BisimplicialModel.internalHomRight.map p) := Lifting.hasLiftingProperty simplexOp
  exact (Adjunction.hasLiftingProperty_iff _root_.SerrePositivity.BisimplicialModel.diagonalInternalHomAdjunction i p).mpr h

/-- Reedy局所化単射の対角がanodyne局所化で可逆となることをKan値テストから導く。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
対角の右随伴と境界内部Homの比較を使い、相対matching射を計算する。
必要な持ち上げ条件またはBrownの補題を、この実際の比較へ適用する。
-/
lemma localized_diagonal_map_of_reedy_localizedMonos {A T : SimplexCategoryᵒᵖ ⥤ SSet.{v}}
    (i : A ⟶ T) (hi : reedyLeft simplexOp KanTestLiftingClass.localizedMonos i) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.BisimplicialModel.diagonal.map i)) := by
  apply KanTestLiftingClass.localized_isIso_of_llp
  intro E B p hp
  obtain ⟨h, hB⟩ := _root_.SerrePositivity.BisimplicialModel.rightTest_kan p hp
  exact diagonal_lifting_of_reedy_localizedMonos i hi p h hB

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72
