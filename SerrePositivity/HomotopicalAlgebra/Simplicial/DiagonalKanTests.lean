module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.OfMap
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestLiftingClass

/-!
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
open SerrePositivity.SimplicialModel
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.BisimplicialModel

lemma rightTest_kan {E B : SSet.{v}} (p : E ⟶ B) (hp : KanTestLiftingClass.rightTests p) :
    SSet.modelCategoryQuillen.J.rlp p ∧
      SSet.modelCategoryQuillen.J.rlp (terminal.from B) := by
  cases hp with
  | terminal K hK =>
    refine ⟨hK, ?_⟩
    have h : terminal.from (⊤_ SSet.{v}) = 𝟙 _ := terminal.hom_ext _ _
    rw [h]
    exact (SSet.modelCategoryQuillen.J.rlp).of_isIso _
  | paths K hK =>
    have : Fibration (terminal.from K) := (SSet.modelCategoryQuillen.fibration_iff _).mpr hK
    have : SSet.KanComplex K := (isFibrant_iff K).mpr inferInstance
    have h : Fibration (KanTestLiftingClass.pathRestriction K).π := SSet.fibration_pullbackObjObjπ _
    have hKan : IsFibrant ((ihom (SSet.boundary 1).toSSet).obj K) := inferInstance
    exact ⟨(SSet.modelCategoryQuillen.fibration_iff _).mp h,
      (SSet.modelCategoryQuillen.fibration_iff _).mp hKan⟩

end SerrePositivity.BisimplicialModel
