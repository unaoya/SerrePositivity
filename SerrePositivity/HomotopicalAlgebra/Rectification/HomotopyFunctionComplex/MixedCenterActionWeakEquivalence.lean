module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.NerveMixedAction

/-!
# 中断した任意モデル源への一般化：MixedCenterActionWeakEquivalence

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Weak equivalences for the same center and whole-chain mixed actions。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0112][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0112
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Weak equivalences for the same center and whole-chain mixed actions
-/

@[expose] public section
universe v u w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence
variable (C : Type u) [Category.{v} C] [ModelCategory C]

lemma recovery (q : MixedResolutionCenters.Index C) {T : SSet.{v}}
    (s : T ⟶ (MixedResolutionCenters.leftChoices C).obj q)
    (r : T ⟶ (MixedResolutionCenters.rightChoices C).obj q)
    (t : T ⟶ (MixedResolutionCenters.input C).obj (op q)) :
    MixedResolutionCenters.action C q s r t =
      MixedResolutionLiftAction.action (ResolutionArrowDiagram.source C q.1).inner
        (ResolutionArrowDiagram.target C q.1) (ResolutionArrowDiagram.arrow C q.1)
        (ResolutionArrowDiagram.source Cᵒᵖ q.2).inner
        (ResolutionArrowDiagram.target Cᵒᵖ q.2) (ResolutionArrowDiagram.arrow Cᵒᵖ q.2)
        (s ≫ (ResolutionArrowDiagram.fiberIso C q.1).hom)
        (r ≫ (ResolutionArrowDiagram.fiberIso Cᵒᵖ q.2).hom) t := by
  unfold MixedResolutionCenters.action MixedResolutionLiftAction.action
  rw [MixedResolutionCenters.family_recovery, MixedResolutionCenters.family_recovery]

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma action_weakEquivalence (q : MixedResolutionCenters.Index C)
    (hf : weakEquivalences C (ResolutionArrowDiagram.arrow C q.1))
    (hg : weakEquivalences Cᵒᵖ (ResolutionArrowDiagram.arrow Cᵒᵖ q.2))
    {T : SSet.{v}} (s : T ⟶ (MixedResolutionCenters.leftChoices C).obj q)
    (r : T ⟶ (MixedResolutionCenters.rightChoices C).obj q)
    (t : T ⟶ (MixedResolutionCenters.input C).obj (op q))
    (ht : weakEquivalences SSet.{v} t) :
    weakEquivalences SSet.{v} (MixedResolutionCenters.action C q s r t) := by
  rw [recovery]
  exact MixedLiftActionWeakEquivalence.action_weakEquivalence _ _ _ _ _ _ hcof hfib hf hg _ _ t ht

include hcof hfib in
lemma kanAction_weakEquivalence (q : MixedResolutionCenters.Index C)
    (hf : weakEquivalences C (ResolutionArrowDiagram.arrow C q.1))
    (hg : weakEquivalences Cᵒᵖ (ResolutionArrowDiagram.arrow Cᵒᵖ q.2))
    {T : SSet.{v}} (s : T ⟶ (MixedResolutionCenters.leftChoices C).obj q)
    (r : T ⟶ (MixedResolutionCenters.rightChoices C).obj q)
    (t : T ⟶ (MixedResolutionCenters.input C).obj (op q))
    (ht : weakEquivalences SSet.{v} t) :
    weakEquivalences SSet.{v} (MixedResolutionCenters.kanAction C hcof hfib q s r t) :=
  (weakEquivalences SSet.{v}).comp_mem _ _
    (action_weakEquivalence C hcof hfib q hf hg s r t ht)
    (KanReplacement.unit_weakEquivalence hcof hfib _)

variable {D : Type uD} [Category.{vD} D] (H : D ⥤ MixedResolutionCenters.Index C)
  (K : D ⥤ SSet.{v})
  (a : NerveMovingParameter.System.{w, v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K)
    (H ⋙ MixedResolutionCenters.leftChoices C))
  (b : NerveMovingParameter.System.{w, v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K)
    (H ⋙ MixedResolutionCenters.rightChoices C))

include a b in
lemma chain_action_weakEquivalence {n : ℕ} (c : ComposableArrows D n)
    (hf : weakEquivalences C
      (ResolutionArrowDiagram.arrow C (NerveMixedAction.center C H c).1))
    (hg : weakEquivalences Cᵒᵖ
      (ResolutionArrowDiagram.arrow Cᵒᵖ (NerveMixedAction.center C H c).2))
    (t : NerveMixedAction.parameter K c ⟶ NerveMixedAction.input C H c)
    (ht : weakEquivalences SSet.{v} t) :
    weakEquivalences SSet.{v} (NerveMixedAction.action C hcof hfib H K a b c t) :=
  kanAction_weakEquivalence C hcof hfib _ hf hg _ _ t ht

end SerrePositivity.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence
