module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedResolutionKanComparison
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedResolutionCenters

/-!
# 中断した任意モデル源への一般化：MixedCenterComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The comparison targets the same whole-center action output。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0113][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0113
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The comparison targets the same whole-center action output

The source projection keeps both actual framed resolutions and all their
maps. The Kan output is literally the existing action's value diagram.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.MixedCenterComparison
variable (C : Type u) [Category.{v} C] [ModelCategory C]

def sources : MixedResolutionCenters.Index C ⥤ RightResolutionMapping.Index C where
  obj q := (op (ResolutionArrowDiagram.source C q.1),
    op (ResolutionArrowDiagram.source Cᵒᵖ q.2))
  map f := (f.1.hom.1, f.2.hom.1)

def outputIso : sources C ⋙ MixedResolutionComparison.output ≅
    MixedResolutionCenters.output C :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro q p f
    ext n h
    rfl)

def comparison : sources C ⋙ MixedBiresolutionComparison.functor ⟶
    MixedResolutionCenters.output C :=
  Functor.whiskerLeft (sources C) MixedResolutionComparison.comparison ≫ (outputIso C).hom

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma comparison_weakEquivalence (q : MixedResolutionCenters.Index C) :
    weakEquivalences SSet.{v} ((comparison C).app q) :=
  (weakEquivalences SSet.{v}).comp_mem _ _
    (MixedResolutionComparison.comparison_weakEquivalence hcof hfib ((sources C).obj q))
    ((weakEquivalences SSet.{v}).of_isIso _)

def kanComparison : sources C ⋙ BalancedResolutionComparison.middle hcof hfib ⟶
    MixedResolutionCenters.kanOutput C hcof hfib :=
  Functor.whiskerLeft (sources C) (MixedResolutionKanComparison.comparison hcof hfib) ≫
    Functor.whiskerRight (outputIso C).hom (KanReplacement.functor hcof hfib)

lemma kanComparison_weakEquivalence (q : MixedResolutionCenters.Index C) :
    weakEquivalences SSet.{v} ((kanComparison C hcof hfib).app q) :=
  (weakEquivalences SSet.{v}).comp_mem _ _
    (MixedResolutionKanComparison.comparison_weakEquivalence hcof hfib ((sources C).obj q))
    ((weakEquivalences SSet.{v}).of_isIso _)

end SerrePositivity.HomotopyFunctionComplex.MixedCenterComparison
