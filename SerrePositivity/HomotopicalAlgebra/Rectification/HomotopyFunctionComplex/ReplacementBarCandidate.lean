module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ReplacementMappingDescent
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarAugmentation

/-!
# 中断した任意モデル源への一般化：ReplacementBarCandidate

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A strict auxiliary bar candidate on both undecorated base variables。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0270][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0270
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A strict auxiliary bar candidate on both undecorated base variables

Its unit and composition laws hold before localization. Its value universe
is max(u,v), not yet the required v. No model structure on that larger
simplicial-set category, Kan property, or comparison weak equivalence is assumed.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- The strict auxiliary object; it is not the final small RMap. -/
abbrev auxiliaryBar : (Cᵒᵖ × C) ⥤ SSet.{max u v} :=
  SimplicialModel.BarConstruction.relative (projection (C := C)) (uncurried hcof hfib)

lemma auxiliaryBar_degree (X : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ) :
    ((auxiliaryBar hcof hfib).obj X).obj n =
    ComposableArrows (CostructuredArrow
      (SimplicialModel.BarConstruction.elementProjection (projection (C := C))
        (uncurried hcof hfib) n) X) n.unop.len := rfl

end SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
