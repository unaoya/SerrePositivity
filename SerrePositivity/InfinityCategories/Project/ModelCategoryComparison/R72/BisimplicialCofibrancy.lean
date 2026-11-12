module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Small.Basic
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SuccPred.Nat
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BisimplicialCofibrancy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.LatchingMonomorphisms


/-!
分割で生成：docstring を書き直すこと
# 標準的な単射cofibration条件のもとで二重単体的集合はReedy cofibrantである

## 概要
標準的な単射cofibration条件のもとで二重単体的集合はReedy cofibrantである。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
latching比較の評価を、余極限を保つ評価関手の同型を介してTypeのlatching比較へ移す。
Eilenberg–Zilberの分解から単射性を導く。

## 規約と注意
モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
このファイルがHT-KQの引用モデルを自動的に選ぶとは解釈しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0351][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0351
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Every bisimplicial set is Reedy cofibrant

Evaluation of the actual latching comparison agrees, through the colimit
preservation isomorphism, with a simplicial-set latching comparison in Type.
Eilenberg--Zilber gives its injectivity. No splitting in SSet is assumed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72

/-- The actual latching comparison commutes with evaluation via colimit preservation. -/
lemma evaluation_comparison (B : SimplexCategoryᵒᵖ ⥤ SSet.{v})
    (j k : SimplexCategoryᵒᵖ) :
    (preservesColimitIso ((evaluation SimplexCategoryᵒᵖ (Type v)).obj k)
      (latchingSource simplexOp j ⋙ B)).inv ≫
      ((latchingComparison simplexOp j).app B).app k =
        (latchingComparison simplexOp j).app (_root_.SerrePositivity.BisimplicialModel.column B k) := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type v)).obj k
  let D := latchingSource simplexOp j ⋙ B
  apply colimit.hom_ext
  intro a
  change colimit.ι (D ⋙ E) a ≫
      ((preservesColimitIso E D).inv ≫ E.map ((latchingComparison simplexOp j).app B)) = _
  rw [← Category.assoc, ι_preservesColimitIso_inv, ← E.map_comp]
  exact (congrArg E.map (colimit.ι_desc (latchingCocone simplexOp B j) a)).trans
    (colimit.ι_desc (latchingCocone simplexOp (_root_.SerrePositivity.BisimplicialModel.column B k) j) a).symm

lemma latchingComparison_mono (B : SimplexCategoryᵒᵖ ⥤ SSet.{v})
    (j : SimplexCategoryᵒᵖ) : Mono ((latchingComparison simplexOp j).app B) := by
  have : ∀ k, Mono (((latchingComparison simplexOp j).app B).app k) := by
    intro k
    let e := preservesColimitIso ((evaluation SimplexCategoryᵒᵖ (Type v)).obj k)
      (latchingSource simplexOp j ⋙ B)
    have : Mono ((latchingComparison simplexOp j).app (_root_.SerrePositivity.BisimplicialModel.column B k)) :=
      SimplicialLatching.comparison_mono _ _
    have he : ((latchingComparison simplexOp j).app B).app k =
        e.hom ≫ (latchingComparison simplexOp j).app (_root_.SerrePositivity.BisimplicialModel.column B k) := by
      rw [← evaluation_comparison B j k]
      exact (Iso.hom_inv_id_assoc e _).symm
    rw [he]
    infer_instance
  exact NatTrans.mono_of_mono_app _

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72
