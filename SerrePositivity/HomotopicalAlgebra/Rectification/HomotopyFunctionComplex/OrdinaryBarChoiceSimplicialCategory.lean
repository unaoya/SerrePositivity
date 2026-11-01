module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceCategory
public import Mathlib.CategoryTheory.Category.Cat

/-!
# 中断した任意モデル源への一般化：OrdinaryBarChoiceSimplicialCategory

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A strict simplicial diagram of categories of relative bar-action lifts。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0144][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0144
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A strict simplicial diagram of categories of relative bar-action lifts

Objects retain the original base objects. Every simplex of morphisms retains
its base arrow and the entire extension family. The diagram is auxiliary
and is not a small SSet-valued strictification on the original base.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceSimplicialCategory
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

def functor : SimplexCategoryᵒᵖ ⥤ Cat.{max u v, u} where
  obj n := Cat.of (OrdinaryBarChoiceCategory.Object (C := C) hcof hfib
    (SSet.stdSimplex.{max u v}.obj n.unop))
  map θ := (OrdinaryBarChoiceCategory.reindex hcof hfib (SSet.stdSimplex.map θ.unop)).toCatHom
  map_id n := by
    apply Cat.ext
    change OrdinaryBarChoiceCategory.reindex hcof hfib (SSet.stdSimplex.map (𝟙 n.unop)) = _
    rw [CategoryTheory.Functor.map_id SSet.stdSimplex, OrdinaryBarChoiceCategory.reindex_id]
    rfl
  map_comp f g := by
    apply Cat.ext
    change OrdinaryBarChoiceCategory.reindex hcof hfib
      (SSet.stdSimplex.map (g.unop ≫ f.unop)) = _
    rw [SSet.stdSimplex.map_comp, OrdinaryBarChoiceCategory.reindex_comp]
    rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceSimplicialCategory
