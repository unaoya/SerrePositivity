module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BarConstruction
public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.Logic.Small.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# 中断した任意モデル源への一般化：BarSize

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Raw bar size can grow even for a diagram of points。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0348][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0348
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Raw bar size can grow even for a diagram of points

The objects of the indexing category inject into degree zero. Consequently
objectwise small input values alone cannot justify shrinking a raw bar.
-/

@[expose] public section
universe v uD vD
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable (D : Type uD) [Category.{vD} D]

abbrev pointDiagram : D ⥤ SSet.{v} :=
  (Functor.const D).obj (SSet.stdSimplex.obj (SimplexCategory.mk 0))

/-- Distinct index objects remain distinct vertices of the raw bar of a point diagram. -/
def indexVertex (d : D) :
    ((functor D).obj (pointDiagram.{v} D)).obj (Opposite.op (SimplexCategory.mk 0)) :=
  ComposableArrows.mk₀ (((pointDiagram.{v} D).flip.obj
    (Opposite.op (SimplexCategory.mk 0))).elementsMk d (SSet.stdSimplex.obj₀Equiv.symm 0))

lemma indexVertex_injective : Function.Injective (indexVertex.{v} D) := by
  intro x y h
  exact congrArg (fun c => (c.obj 0).obj) h

lemma index_small_of_bar_zero_small
    [Small.{v} (((functor D).obj (pointDiagram.{v} D)).obj
      (Opposite.op (SimplexCategory.mk 0)))] : Small.{v} D :=
  small_of_injective (indexVertex_injective.{v} D)

/-- No model structure or weak-equivalence assertion is involved in the size obstruction. -/
lemma point_bar_not_small :
    ¬ Small.{v} (((functor (Codiscrete (Type v))).obj
      (pointDiagram.{v} (Codiscrete (Type v)))).obj (Opposite.op (SimplexCategory.mk 0))) := by
  intro h
  have := h
  have : Small.{v} (Codiscrete (Type v)) :=
    index_small_of_bar_zero_small.{v} (Codiscrete (Type v))
  apply not_small_type.{v, 0}
  exact small_of_injective (f := fun A : Type v => Codiscrete.mk A)
    (fun _ _ h => congrArg Codiscrete.as h)

end SerrePositivity.SimplicialModel.BarConstruction
