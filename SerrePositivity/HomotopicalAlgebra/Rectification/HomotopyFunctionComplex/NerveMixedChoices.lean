module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.NerveMixedAction
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveMovingParameter

/-!
# 中断した任意モデル源への一般化：NerveMixedChoices

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual coherent choices for both centers with the original families retained。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0130][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0130
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual coherent choices for both centers with the original families retained

Only the original small lift spaces supply fillers. Parameters and the
index may be large; no larger simplicial model structure is used.
-/

@[expose] public section
universe v u w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.NerveMixedChoices
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  {D : Type uD} [Category.{vD} D] (H : D ⥤ MixedResolutionCenters.Index C)
  (K : D ⥤ SSet.{v})

def leftSystem (families : ∀ d, K.obj d ⟶ (MixedResolutionCenters.leftChoices C).obj (H.obj d)) :
    NerveMovingParameter.System.{w, v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K)
      (H ⋙ MixedResolutionCenters.leftChoices C) :=
  NerveMovingParameter.extendFamilies _ _
    (fun d => ResolutionArrowDiagram.fillers C hcof (H.obj d).1)
    (fun d => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w, v} (families d))

def rightSystem
    (families : ∀ d, K.obj d ⟶ (MixedResolutionCenters.rightChoices C).obj (H.obj d)) :
    NerveMovingParameter.System.{w, v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K)
      (H ⋙ MixedResolutionCenters.rightChoices C) :=
  NerveMovingParameter.extendFamilies _ _
    (fun d => ResolutionArrowDiagram.fillers Cᵒᵖ hcof (H.obj d).2)
    (fun d => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w, v} (families d))

lemma left_point
    (families : ∀ d, K.obj d ⟶ (MixedResolutionCenters.leftChoices C).obj (H.obj d)) (d : D) :
    NerveSmallFamilies.point K (H ⋙ MixedResolutionCenters.leftChoices C)
      (leftSystem.{v, u, w} C hcof H K families) d = families d := by
  unfold NerveSmallFamilies.point leftSystem
  rw [NerveMovingParameter.extendFamilies_evaluate]
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower_map _

lemma right_point
    (families : ∀ d, K.obj d ⟶ (MixedResolutionCenters.rightChoices C).obj (H.obj d)) (d : D) :
    NerveSmallFamilies.point K (H ⋙ MixedResolutionCenters.rightChoices C)
      (rightSystem.{v, u, w} C hcof H K families) d = families d := by
  unfold NerveSmallFamilies.point rightSystem
  rw [NerveMovingParameter.extendFamilies_evaluate]
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower_map _

def selectedLeft : NerveMovingParameter.System.{w, v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K)
    (H ⋙ MixedResolutionCenters.leftChoices C) :=
  leftSystem C hcof H K (fun d => SSet.stdSimplex.isTerminalObj₀.from (K.obj d) ≫
    ResolutionArrowDiagram.selectedPoint C (H.obj d).1)

def selectedRight : NerveMovingParameter.System.{w, v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K)
    (H ⋙ MixedResolutionCenters.rightChoices C) :=
  rightSystem C hcof H K (fun d => SSet.stdSimplex.isTerminalObj₀.from (K.obj d) ≫
    ResolutionArrowDiagram.selectedPoint Cᵒᵖ (H.obj d).2)

def extendLeft (n : ℕ) (old : NerveMovingParameter.LowerSystem
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K) (H ⋙ MixedResolutionCenters.leftChoices C) n) :
    NerveMovingParameter.System.{w, v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K)
      (H ⋙ MixedResolutionCenters.leftChoices C) :=
  NerveMovingParameter.extend _ _
    (fun d => ResolutionArrowDiagram.fillers C hcof (H.obj d).1) n old

def extendRight (n : ℕ) (old : NerveMovingParameter.LowerSystem
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K) (H ⋙ MixedResolutionCenters.rightChoices C) n) :
    NerveMovingParameter.System.{w, v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K)
      (H ⋙ MixedResolutionCenters.rightChoices C) :=
  NerveMovingParameter.extend _ _
    (fun d => ResolutionArrowDiagram.fillers Cᵒᵖ hcof (H.obj d).2) n old

lemma extendLeft_restrict (n : ℕ) (old : NerveMovingParameter.LowerSystem
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K) (H ⋙ MixedResolutionCenters.leftChoices C) n) :
    Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n)
      (extendLeft C hcof H K n old) = old :=
  NerveMovingParameter.extend_restrict _ _ _ n old

lemma extendRight_restrict (n : ℕ) (old : NerveMovingParameter.LowerSystem
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K) (H ⋙ MixedResolutionCenters.rightChoices C) n) :
    Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n)
      (extendRight C hcof H K n old) = old :=
  NerveMovingParameter.extend_restrict _ _ _ n old

end SerrePositivity.HomotopyFunctionComplex.NerveMixedChoices
