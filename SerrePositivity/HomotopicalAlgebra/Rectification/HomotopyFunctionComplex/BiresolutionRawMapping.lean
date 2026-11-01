module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.RightResolutionMapping

/-!
# 中断した任意モデル源への一般化：BiresolutionRawMapping

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual double Hom before either Kan comparison。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0061][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0061
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual double Hom before either Kan comparison

The diagonal uses maps A[n] to B[n], in the original Hom universe.
Its comparison to the source-framed diagonal is natural on the entire index.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.BiresolutionRawMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev rawUncurried : ReplacementMapping.Index C ⥤ SSet.{v} :=
  Functor.uncurry.obj (ReplacementMapping.raw (C := C))

abbrev rows : SimplexCategoryᵒᵖ ⥤ RightResolutionMapping.Index C ⥤ SSet.{v} :=
  RightResolutionMapping.presentationRows ⋙
    (Functor.whiskeringRight (RightResolutionMapping.Index C)
      (ReplacementMapping.Index C) SSet.{v}).obj rawUncurried

abbrev functor : RightResolutionMapping.Index C ⥤ SSet.{v} :=
  (rows (C := C)).flip ⋙ BisimplicialModel.diagonal

lemma simplex_type (X : RightResolutionMapping.Index C) (n : SimplexCategoryᵒᵖ) :
    ((functor (C := C)).obj X).obj n =
      (X.1.unop.inner.resolution.obj.obj n.unop ⟶
        (DualResolutionTargets.diagram C ((DualResolutionTargets.framedForget C).obj X.2)).obj n) :=
  rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev uncurriedComparison : rawUncurried (C := C) ⟶
    ReplacementMapping.uncurried hcof hfib :=
  Functor.uncurry.map (ReplacementMapping.comparison hcof hfib)

def rowsComparison : rows (C := C) ⟶ RightResolutionMapping.rows hcof hfib where
  app n := Functor.whiskerLeft (RightResolutionMapping.presentationRows.obj n)
    (uncurriedComparison hcof hfib)
  naturality {n m} f := by
    apply NatTrans.ext
    funext X
    exact (uncurriedComparison hcof hfib).naturality
      ((RightResolutionMapping.presentationRows.map f).app X)

/-- The full raw diagonal compares to the existing left-framed diagonal. -/
def comparison : functor (C := C) ⟶ RightResolutionMapping.functor hcof hfib :=
  Functor.whiskerRight
    ((CategoryTheory.flipFunctor SimplexCategoryᵒᵖ (RightResolutionMapping.Index C) SSet.{v}).map
      (rowsComparison hcof hfib)) BisimplicialModel.diagonal

lemma comparison_weakEquivalence (X : RightResolutionMapping.Index C) :
    weakEquivalences SSet.{v} ((comparison hcof hfib).app X) := by
  apply BisimplicialModel.diagonal_map_weakEquivalence hcof hfib
  intro n
  exact ReplacementMapping.comparison_weakEquivalence hcof hfib X.1
    ((DualResolutionTargets.framedPresentation C n).obj X.2)

end SerrePositivity.HomotopyFunctionComplex.BiresolutionRawMapping
