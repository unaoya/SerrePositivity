module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.SelectedIntervalEndpoints

/-!
# 中断した任意モデル源への一般化：SelectedIntervalVertices

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The entire vertex cylinder remains fixed in the same selected interval system。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0335][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0335
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The entire vertex cylinder remains fixed in the same selected interval system
-/

@[expose] public section
universe v u uE vE
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open NerveBiparameterMaps

namespace SerrePositivity.HomotopyFunctionComplex.SelectedIntervalVertices
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev vertices := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product
  (ResolutionArrowComparisonEndpoints.vertexParameter C)
  ResolutionArrowCylinderBoundary.interval.{max u v}
abbrev horizontal : vertices C ⟶ ResolutionArrowCylinderBoundary.fullParameter C :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (ResolutionArrowComparisonEndpoints.vertexParameter C)
    (ResolutionArrowComparisonEndpoints.parameter C)
    (ResolutionArrowComparisonEndpoints.vertexInclusion C)
    ResolutionArrowCylinderBoundary.interval.{max u v}

lemma coherent_vertices : SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction
    (SelectedIntervalDiagram.forget C ⋙ vertices C) (SelectedIntervalDiagram.parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
    (Functor.whiskerLeft (SelectedIntervalDiagram.forget C) (horizontal C)) =
    reindex (vertices C)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (ResolutionArrowComparisonEndpoints.values C))
      (SelectedIntervalDiagram.forget C) (ResolutionArrowCylinderBoundary.vertices C) := by
  change SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal _ _ _ _)) = _
  rw [← NerveCylinderBoundary.vertexInclusion_inclusion
    (ResolutionArrowComparisonEndpoints.vertexParameter C)
    (ResolutionArrowComparisonEndpoints.parameter C)
    (ResolutionArrowComparisonEndpoints.vertexInclusion C)
    ResolutionArrowCylinderBoundary.boundaryMap.{max u v}]
  change SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
      (NerveCylinderBoundary.vertexInclusion _ _ _ _) ≫
        SelectedIntervalDiagram.boundaryInclusion C) = _
  have hb : SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction
      (SelectedIntervalDiagram.boundaries C) (SelectedIntervalDiagram.parameters C)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
      (SelectedIntervalDiagram.boundaryInclusion C) =
      SelectedIntervalDiagram.fixedBoundary C hcof :=
    SelectedIntervalDiagram.coherent_boundary C hcof hfib
  rw [← restriction_comp, ← Category.assoc, hb]
  change reindex _ _ (SelectedIntervalDiagram.forget C)
    (ResolutionArrowCylinderBoundary.system C hcof) ≫ restriction _ _ _
      (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
        (NerveCylinderBoundary.vertexInclusion _ _ _ _)) = _
  rw [← reindex_restriction, ResolutionArrowCylinderBoundary.system_vertices]

variable {E : Type uE} [Category.{vE} E] (H : E ⥤ SelectedIntervalDiagram.Index C)

lemma reindexed_vertices : reindex (SelectedIntervalDiagram.parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) H
      (SelectedIntervalDiagram.coherent C hcof hfib) ≫ restriction _ _ _
        (Functor.whiskerLeft H
          (Functor.whiskerLeft (SelectedIntervalDiagram.forget C) (horizontal C))) =
    NerveNaturalBoundary.ofNatTrans _ _ (Functor.whiskerLeft
      (H ⋙ SelectedIntervalDiagram.forget C)
      (NerveProductParameter.projection (ResolutionArrowComparisonEndpoints.vertexParameter C)
        ResolutionArrowCylinderBoundary.interval.{max u v} ≫
          ResolutionArrowComparisonEndpoints.vertexBoundary C)) := by
  rw [← reindex_restriction, coherent_vertices]
  apply (reindex_reindex (vertices C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (ResolutionArrowComparisonEndpoints.values C))
    (SelectedIntervalDiagram.forget C) H (ResolutionArrowCylinderBoundary.vertices C)).trans
  exact reindex_natural _ _ _ _

end SerrePositivity.HomotopyFunctionComplex.SelectedIntervalVertices
