module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedDiagonalData

/-!
# 中断した任意モデル源への一般化：ResolutionMixedCoherentDiagonal

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The same selected mixed diagonal as one coherent family with both whole endpoints fixed。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0314][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0314
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The same selected mixed diagonal as one coherent family with both whole endpoints fixed
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedIntervalRestrictions ResolutionMixedRawEndpoints
open ResolutionMixedDiagonalData NerveBiparameterMaps

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev boundaryParameters := arrowFunctor C ⋙ ResolutionArrowCylinderBoundary.boundaryParameter C
abbrev boundaryInclusion : boundaryParameters C ⟶ intervalParameters C :=
  Functor.whiskerLeft (arrowFunctor C) (ResolutionArrowCylinderBoundary.inclusion C)
abbrev fixedBoundary : NerveMovingParameter.System.{u, v} (boundaryParameters C) (smallValues C) :=
  reindex _ _ (arrowFunctor C) (ResolutionArrowCylinderBoundary.system C hcof)

lemma family_fit (p : Index C) : (boundaryInclusion C).app p ≫ family C hcof hfib p =
    NerveMovingParameter.evaluate (boundaryParameters C) (smallValues C) (fixedBoundary C hcof) p :=
  (fit C hcof hfib p).trans (evaluate_reindex
    (ResolutionArrowCylinderBoundary.boundaryParameter C) (ResolutionArrowComparisonEndpoints.values
      C)
      (ResolutionArrowCylinderBoundary.system C hcof) (arrowFunctor C) p).symm

/-- Keep the old complete diagonal and the same full Q-boundary, without another compatibility
  input. -/
def coherent : NerveMovingParameter.System.{u, v} (intervalParameters C) (smallValues C) :=
  NerveMovingFamilyFit.extend (intervalParameters C) (smallValues C) (boundaryParameters C)
    (boundaryInclusion C) (family C hcof hfib) (fixedBoundary C hcof) (family_fit C hcof hfib)
    (fun p => ResolutionArrowDiagram.fillers C hcof (d C p))
    (fun p => ResolutionArrowCylinderBoundary.inclusion_mono C ((arrowFunctor C).obj p))

lemma coherent_evaluate (p : Index C) : NerveMovingParameter.evaluate (intervalParameters C)
    (smallValues C) (coherent C hcof hfib) p = family C hcof hfib p :=
  NerveMovingFamilyFit.extend_evaluate _ _ _ _ _ _ _ _ _ p

lemma coherent_boundary : coherent C hcof hfib ≫ restriction (boundaryParameters C)
    (intervalParameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (boundaryInclusion C) =
      fixedBoundary C hcof := NerveMovingFamilyFit.extend_boundary _ _ _ _ _ _ _ _ _

lemma coherent_recover (p : Index C) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor
    (NerveMovingParameter.evaluate (intervalParameters C) (smallValues C) (coherent C hcof hfib) p)
      =
    RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
      (ResolutionMixedTriangles.oldBoundary C p) (ResolutionMixedTriangles.oldDiagonal C hcof hfib
        p) :=
  (congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor (coherent_evaluate C hcof hfib p)).trans
    (ResolutionMixedDiagonalData.recover C hcof hfib p)

lemma coherent_zero : ResolutionMixedEndpointCompatibility.endpoint C (coherent C hcof hfib) 1 =
    ResolutionMixedEndpointCompatibility.expand C
      (ResolutionMixedEndpointCompatibility.corner0 C hcof) := by
  change coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (arrowFunctor C)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (1 : Fin 2))
        (ResolutionArrowComparisonEndpoints.parameter C))) = _
  rw [← ResolutionArrowCylinderFaces.zero]
  change coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (arrowFunctor C) (ResolutionArrowCylinderBoundary.zeroInclusion C) ≫
      boundaryInclusion C) = _
  rw [← restriction_comp, ← Category.assoc, coherent_boundary]
  change reindex _ _ (arrowFunctor C) (ResolutionArrowCylinderBoundary.system C hcof) ≫
    restriction _ _ _ (Functor.whiskerLeft (arrowFunctor C)
      (ResolutionArrowCylinderBoundary.zeroInclusion C)) = _
  rw [← reindex_restriction, ResolutionArrowCylinderBoundary.system_zero, reindex_expand]
  exact congrArg (fun a => NerveProductParameter.expand (parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) a)
        (NerveArrowComparisonComposition.left_reindex (K C) (F C) (chosen C hcof) (arrowFunctor C))

lemma coherent_one : ResolutionMixedEndpointCompatibility.endpoint C (coherent C hcof hfib) 0 =
    ResolutionMixedEndpointCompatibility.expand C
      (ResolutionMixedEndpointCompatibility.corner3 C hcof) := by
  change coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (arrowFunctor C)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (0 : Fin 2))
        (ResolutionArrowComparisonEndpoints.parameter C))) = _
  rw [← ResolutionArrowCylinderFaces.one]
  change coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (arrowFunctor C) (ResolutionArrowCylinderBoundary.oneInclusion C) ≫
      boundaryInclusion C) = _
  rw [← restriction_comp, ← Category.assoc, coherent_boundary]
  change reindex _ _ (arrowFunctor C) (ResolutionArrowCylinderBoundary.system C hcof) ≫
    restriction _ _ _ (Functor.whiskerLeft (arrowFunctor C)
      (ResolutionArrowCylinderBoundary.oneInclusion C)) = _
  rw [← reindex_restriction, ResolutionArrowCylinderBoundary.system_one, reindex_expand]
  exact congrArg (fun a => NerveProductParameter.expand (parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) a)
        (NerveArrowComparisonComposition.right_reindex (K C) (F C) (chosen C hcof) (arrowFunctor C))


lemma coherent_vertices : coherent C hcof hfib ≫ restriction
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (vertexParameters C)
      ResolutionArrowCylinderBoundary.interval.{max u v})
    (intervalParameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (vertexParameters C) (parameters C)
      (ResolutionMixedDiagram.vertexInclusion C)
      ResolutionArrowCylinderBoundary.interval.{max u v}) =
    NerveNaturalBoundary.ofNatTrans _ _
      (NerveProductParameter.projection (vertexParameters C)
        ResolutionArrowCylinderBoundary.interval.{max u v} ≫
          ResolutionMixedDiagram.vertexBoundary C) := by
  change coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (arrowFunctor C)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal
        (ResolutionArrowComparisonEndpoints.vertexParameter C)
        (ResolutionArrowComparisonEndpoints.parameter C)
        (ResolutionArrowComparisonEndpoints.vertexInclusion C)
        ResolutionArrowCylinderBoundary.interval.{max u v})) = _
  rw [← NerveCylinderBoundary.vertexInclusion_inclusion
    (ResolutionArrowComparisonEndpoints.vertexParameter C)
    (ResolutionArrowComparisonEndpoints.parameter C)
    (ResolutionArrowComparisonEndpoints.vertexInclusion C)
    ResolutionArrowCylinderBoundary.boundaryMap.{max u v}]
  change coherent C hcof hfib ≫ restriction _ _ _
    (Functor.whiskerLeft (arrowFunctor C)
      (NerveCylinderBoundary.vertexInclusion
        (ResolutionArrowComparisonEndpoints.vertexParameter C)
        (ResolutionArrowComparisonEndpoints.parameter C)
        (ResolutionArrowComparisonEndpoints.vertexInclusion C)
        ResolutionArrowCylinderBoundary.boundaryMap.{max u v}) ≫ boundaryInclusion C) = _
  rw [← restriction_comp, ← Category.assoc, coherent_boundary]
  change reindex _ _ (arrowFunctor C) (ResolutionArrowCylinderBoundary.system C hcof) ≫
    restriction _ _ _ (Functor.whiskerLeft (arrowFunctor C)
      (NerveCylinderBoundary.vertexInclusion
        (ResolutionArrowComparisonEndpoints.vertexParameter C)
        (ResolutionArrowComparisonEndpoints.parameter C)
        (ResolutionArrowComparisonEndpoints.vertexInclusion C)
        ResolutionArrowCylinderBoundary.boundaryMap.{max u v})) = _
  rw [← reindex_restriction, ResolutionArrowCylinderBoundary.system_vertices]
  exact reindex_natural _ _ _ _

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal
