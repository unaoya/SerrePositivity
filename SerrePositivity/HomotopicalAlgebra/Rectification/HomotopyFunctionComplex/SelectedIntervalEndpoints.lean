module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.SelectedIntervalDiagram
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveArrowComparisonComposition

/-!
# 中断した任意モデル源への一般化：SelectedIntervalEndpoints

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Both entire endpoint systems of the same selected interval diagram。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0334][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0334
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Both entire endpoint systems of the same selected interval diagram
-/

@[expose] public section
universe v u uE vE
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open NerveBiparameterMaps

namespace SerrePositivity.HomotopyFunctionComplex.SelectedIntervalEndpoints
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev baseParameters := SelectedIntervalDiagram.forget C ⋙
  ResolutionArrowComparisonEndpoints.parameter C
abbrev pointParameters := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (baseParameters C)
  (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))
abbrev faceMap (ε : Fin 2) : pointParameters C ⟶ SelectedIntervalDiagram.parameters C :=
  Functor.whiskerLeft (SelectedIntervalDiagram.forget C) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical
    (SSet.stdSimplex.δ ε) (ResolutionArrowComparisonEndpoints.parameter C))

abbrev left : NerveMovingParameter.System.{u, v} (baseParameters C)
    (SelectedIntervalDiagram.smallValues C) :=
  reindex _ _ (SelectedIntervalDiagram.forget C) (ResolutionArrowComparisonEndpoints.left C hcof)
abbrev right : NerveMovingParameter.System.{u, v} (baseParameters C)
    (SelectedIntervalDiagram.smallValues C) :=
  reindex _ _ (SelectedIntervalDiagram.forget C) (ResolutionArrowComparisonEndpoints.right C hcof)

lemma coherent_zero : SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction
    (pointParameters C) (SelectedIntervalDiagram.parameters C)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) (faceMap C 1) =
    NerveProductParameter.expand (baseParameters C)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
        (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (left C hcof) := by
  have hb : SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction
      (SelectedIntervalDiagram.boundaries C) (SelectedIntervalDiagram.parameters C)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
          (SelectedIntervalDiagram.boundaryInclusion C) =
      SelectedIntervalDiagram.fixedBoundary C hcof :=
    SelectedIntervalDiagram.coherent_boundary C hcof hfib
  change SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (1 : Fin 2))
        (ResolutionArrowComparisonEndpoints.parameter C))) = _
  rw [← ResolutionArrowCylinderFaces.zero]
  change SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
      (ResolutionArrowCylinderBoundary.zeroInclusion C) ≫
        SelectedIntervalDiagram.boundaryInclusion C) = _
  rw [← restriction_comp, ← Category.assoc, hb]
  change reindex _ _ (SelectedIntervalDiagram.forget C)
    (ResolutionArrowCylinderBoundary.system C hcof) ≫ restriction _ _ _
      (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
        (ResolutionArrowCylinderBoundary.zeroInclusion C)) = _
  rw [← reindex_restriction, ResolutionArrowCylinderBoundary.system_zero, reindex_expand]
  rfl

lemma coherent_one : SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction
    (pointParameters C) (SelectedIntervalDiagram.parameters C)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) (faceMap C 0) =
    NerveProductParameter.expand (baseParameters C)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
        (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (right C hcof) := by
  have hb : SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction
      (SelectedIntervalDiagram.boundaries C) (SelectedIntervalDiagram.parameters C)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
          (SelectedIntervalDiagram.boundaryInclusion C) =
      SelectedIntervalDiagram.fixedBoundary C hcof :=
    SelectedIntervalDiagram.coherent_boundary C hcof hfib
  change SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (0 : Fin 2))
        (ResolutionArrowComparisonEndpoints.parameter C))) = _
  rw [← ResolutionArrowCylinderFaces.one]
  change SelectedIntervalDiagram.coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
      (ResolutionArrowCylinderBoundary.oneInclusion C) ≫
        SelectedIntervalDiagram.boundaryInclusion C) = _
  rw [← restriction_comp, ← Category.assoc, hb]
  change reindex _ _ (SelectedIntervalDiagram.forget C)
    (ResolutionArrowCylinderBoundary.system C hcof) ≫ restriction _ _ _
      (Functor.whiskerLeft (SelectedIntervalDiagram.forget C)
        (ResolutionArrowCylinderBoundary.oneInclusion C)) = _
  rw [← reindex_restriction, ResolutionArrowCylinderBoundary.system_one, reindex_expand]
  rfl

variable {E : Type uE} [Category.{vE} E] (B : E ⥤ SelectedIntervalDiagram.Index C)

lemma reindex_left : reindex (baseParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) B (left C hcof) =
    NerveArrowComparisonComposition.leftAlong (ResolutionArrowTupleCoherence.bigTuples C)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (ResolutionArrowDiagram.fibers C))
      (ResolutionArrowTupleCoherence.system C hcof)
      ((B ⋙ SelectedIntervalDiagram.forget C) ⋙ Arrow.leftFunc)
      ((B ⋙ SelectedIntervalDiagram.forget C) ⋙ Arrow.rightFunc)
      (Functor.whiskerLeft (B ⋙ SelectedIntervalDiagram.forget C) Arrow.leftToRight) := by
  change reindex _ _ B (reindex _ _ (SelectedIntervalDiagram.forget C)
    (NerveArrowComparison.left _ _ (ResolutionArrowTupleCoherence.system C hcof))) = _
  rw [reindex_reindex, NerveArrowComparisonComposition.left_reindex]

lemma reindex_right : reindex (baseParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) B (right C hcof) =
    NerveArrowComparisonComposition.rightAlong (ResolutionArrowTupleCoherence.bigTuples C)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (ResolutionArrowDiagram.fibers C))
      (ResolutionArrowTupleCoherence.system C hcof)
      ((B ⋙ SelectedIntervalDiagram.forget C) ⋙ Arrow.leftFunc)
      ((B ⋙ SelectedIntervalDiagram.forget C) ⋙ Arrow.rightFunc)
      (Functor.whiskerLeft (B ⋙ SelectedIntervalDiagram.forget C) Arrow.leftToRight) := by
  change reindex _ _ B (reindex _ _ (SelectedIntervalDiagram.forget C)
    (NerveArrowComparison.right _ _ (ResolutionArrowTupleCoherence.system C hcof))) = _
  rw [reindex_reindex, NerveArrowComparisonComposition.right_reindex]

lemma reindexed_zero : reindex (SelectedIntervalDiagram.parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) B
      (SelectedIntervalDiagram.coherent C hcof hfib) ≫ restriction _ _ _
        (Functor.whiskerLeft B (faceMap C 1)) =
    NerveProductParameter.expand (B ⋙ baseParameters C)
      (B ⋙ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
        (SSet.stdSimplex.obj (SimplexCategory.mk 0))
          (reindex (baseParameters C)
            (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) B
              (left C hcof)) := by
  rw [← reindex_restriction, coherent_zero, reindex_expand]

lemma reindexed_one : reindex (SelectedIntervalDiagram.parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) B
      (SelectedIntervalDiagram.coherent C hcof hfib) ≫ restriction _ _ _
        (Functor.whiskerLeft B (faceMap C 0)) =
    NerveProductParameter.expand (B ⋙ baseParameters C)
      (B ⋙ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C))
        (SSet.stdSimplex.obj (SimplexCategory.mk 0))
          (reindex (baseParameters C)
            (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (SelectedIntervalDiagram.smallValues C)) B
              (right C hcof)) := by
  rw [← reindex_restriction, coherent_one, reindex_expand]

end SerrePositivity.HomotopyFunctionComplex.SelectedIntervalEndpoints
