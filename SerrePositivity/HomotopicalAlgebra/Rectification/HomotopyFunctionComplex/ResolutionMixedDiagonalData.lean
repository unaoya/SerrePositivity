module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedTriangles
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowCylinderFamilyFit

/-!
# 中断した任意モデル源への一般化：ResolutionMixedDiagonalData

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The already selected mixed diagonal fits the same whole endpoint and vertex boundary。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0316][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0316
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The already selected mixed diagonal fits the same whole endpoint and vertex boundary
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open HomotopicalAlgebra SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedIntervalRestrictions

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedDiagonalData
variable (C : Type u) [Category.{v} C] [ModelCategory C]

def arrowFunctor : Index C ⥤ Arrow (ResolutionArrowDiagram.Index C) where
  obj p := Arrow.mk ((ResolutionMixedDiagram.diagonal C).app p)
  map k := Arrow.homMk ((cornerA C).map k) ((cornerD C).map k)
    ((ResolutionMixedDiagram.diagonal C).naturality k)
  map_id _ := rfl
  map_comp _ _ := rfl

lemma fibers (p : Index C) : (ResolutionArrowDiagram.fibers C).map
    ((ResolutionMixedDiagram.diagonal C).app p) =
    ResolutionLiftPostcomposition.map p.middle.inner p.target p.final p.center p.post ≫
      CoherentLiftMixedComparison.preTail p.source.inner p.middle.inner p.target p.final
        p.pre.map p.center p.post (FramedResolution.frameMap p.pre) := by
  apply (congrArg (fun k => (ResolutionArrowDiagram.fibers C).map k) (commutes C p)).trans
  apply ((ResolutionArrowDiagram.fibers C).map_comp (ac C p) (cd C p)).trans
  exact congrArg₂ (fun x y => x ≫ y)
    (ResolutionArrowElementary.post_fibers p.middle p.target p.final p.center p.post)
    (ResolutionArrowElementary.pre_fibers p.source p.middle p.final p.pre
      (p.center ≫ p.post.base))

lemma tuples (p : Index C) : (ResolutionArrowTuples.tuples C).map
    ((ResolutionMixedDiagram.diagonal C).app p) =
    CoherentLiftMixedComparison.tuplePost p.middle.inner p.target p.final p.center p.post ≫
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (CoherentLiftRelative.preStrict p.source.inner p.middle.inner p.final
        p.pre.map (p.center ≫ p.post.base)) := by
  apply (congrArg (fun k => (ResolutionArrowTuples.tuples C).map k) (commutes C p)).trans
  apply ((ResolutionArrowTuples.tuples C).map_comp (ac C p) (cd C p)).trans
  exact congrArg₂ (fun x y => x ≫ y)
    (ResolutionArrowElementary.post_tuples p.middle p.target p.final p.center p.post)
    (ResolutionArrowElementary.pre_tuples p.source p.middle p.final p.pre
      (p.center ≫ p.post.base))

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (p : Index C)

abbrev first := CoherentLiftMixedComparison.familyA hcof p.source.inner p.middle.inner p.target
  p.final p.pre.map p.center p.post (FramedResolution.frameMap p.pre)
abbrev last := CoherentLiftMixedComparison.familyD hcof p.source.inner p.middle.inner p.target
  p.final p.pre.map p.center p.post

abbrev oldHomotopy := RelativeChoiceSpace.FixedBoundaryHomotopy.ofEdge
  (ResolutionMixedTriangles.oldInclusion C p) (ResolutionMixedTriangles.oldBoundary C p)
  (first C hcof p) (last C hcof p)
  (CoherentLiftMixedComparison.familyA_vertices hcof p.source.inner p.middle.inner p.target
    p.final p.pre.map p.center p.post (FramedResolution.frameMap p.pre))
  (CoherentLiftMixedComparison.familyD_vertices hcof p.source.inner p.middle.inner p.target
    p.final p.pre.map p.center p.post (FramedResolution.frameMap p.pre))
  (ResolutionMixedTriangles.oldDiagonal C hcof hfib p)
  (CoherentLiftMixedComparison.diagonal_zero hcof hfib p.source.inner p.middle.inner p.target
    p.final p.pre.map p.center p.post (FramedResolution.frameMap p.pre))
  (CoherentLiftMixedComparison.diagonal_one hcof hfib p.source.inner p.middle.inner p.target
    p.final p.pre.map p.center p.post (FramedResolution.frameMap p.pre))

abbrev family : (intervalParameters C).obj p ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} ((smallValues C).obj p) :=
  UniverseLift.fixedHomotopyMap.{u} (oldHomotopy C hcof hfib p)

lemma left_recover : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower (NerveMovingParameter.evaluate
    (ResolutionArrowComparisonEndpoints.parameter C) (ResolutionArrowComparisonEndpoints.values C)
    (ResolutionArrowComparisonEndpoints.left C hcof) ((arrowFunctor C).obj p)) = first C hcof p :=
      by
  apply (ResolutionArrowComparisonEndpoints.left_recover C hcof ((arrowFunctor C).obj p)).trans
  apply (congrArg (fun k => CoherentLiftTuples.interpolation hcof p.middle.inner p.target
    p.center ≫ k) (fibers C p)).trans
  exact (Category.assoc _ _ _).symm

lemma right_recover : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower (NerveMovingParameter.evaluate
    (ResolutionArrowComparisonEndpoints.parameter C) (ResolutionArrowComparisonEndpoints.values C)
    (ResolutionArrowComparisonEndpoints.right C hcof) ((arrowFunctor C).obj p)) = last C hcof p :=
      by
  apply (ResolutionArrowComparisonEndpoints.right_recover C hcof ((arrowFunctor C).obj p)).trans
  apply (congrArg (fun k => k ≫ CoherentLiftTuples.interpolation hcof p.source.inner p.final
    (p.pre.map.base ≫ p.center ≫ p.post.base)) (tuples C p)).trans
  exact Category.assoc _ _ _

lemma left_lifted : NerveMovingParameter.evaluate (ResolutionArrowComparisonEndpoints.parameter C)
    (ResolutionArrowComparisonEndpoints.values C) (ResolutionArrowComparisonEndpoints.left C hcof)
    ((arrowFunctor C).obj p) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (first C hcof p) :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_lower _).symm.trans (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} k)
    (left_recover C hcof p))

lemma right_lifted : NerveMovingParameter.evaluate (ResolutionArrowComparisonEndpoints.parameter C)
    (ResolutionArrowComparisonEndpoints.values C) (ResolutionArrowComparisonEndpoints.right C hcof)
    ((arrowFunctor C).obj p) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (last C hcof p) :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_lower _).symm.trans (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} k)
    (right_recover C hcof p))

lemma zero : (ResolutionArrowCylinderBoundary.zeroInclusion C ≫
    ResolutionArrowCylinderBoundary.inclusion C).app ((arrowFunctor C).obj p) ≫ family C hcof hfib p
      =
    (NerveProductParameter.projection (ResolutionArrowComparisonEndpoints.parameter C)
      NerveMovingIntervalBoundary.point).app ((arrowFunctor C).obj p) ≫
    NerveMovingParameter.evaluate (ResolutionArrowComparisonEndpoints.parameter C)
      (ResolutionArrowComparisonEndpoints.values C) (ResolutionArrowComparisonEndpoints.left C hcof)
        ((arrowFunctor C).obj p) := by
  rw [ResolutionArrowCylinderFaces.zero]
  exact (UniverseLift.fixedHomotopyMap_zero.{u} (oldHomotopy C hcof hfib p)).trans
    (congrArg (fun k => fst _ _ ≫ k) (left_lifted C hcof p).symm)

lemma one : (ResolutionArrowCylinderBoundary.oneInclusion C ≫
    ResolutionArrowCylinderBoundary.inclusion C).app ((arrowFunctor C).obj p) ≫ family C hcof hfib p
      =
    (NerveProductParameter.projection (ResolutionArrowComparisonEndpoints.parameter C)
      NerveMovingIntervalBoundary.point).app ((arrowFunctor C).obj p) ≫
    NerveMovingParameter.evaluate (ResolutionArrowComparisonEndpoints.parameter C)
      (ResolutionArrowComparisonEndpoints.values C) (ResolutionArrowComparisonEndpoints.right C
        hcof)
        ((arrowFunctor C).obj p) := by
  rw [ResolutionArrowCylinderFaces.one]
  exact (UniverseLift.fixedHomotopyMap_one.{u} (oldHomotopy C hcof hfib p)).trans
    (congrArg (fun k => fst _ _ ≫ k) (right_lifted C hcof p).symm)

lemma vertex : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal
    (ResolutionArrowComparisonEndpoints.vertexParameter C)
      (ResolutionArrowComparisonEndpoints.parameter C)
    (ResolutionArrowComparisonEndpoints.vertexInclusion C)
      ResolutionArrowCylinderBoundary.interval.{max u v}).app ((arrowFunctor C).obj p) ≫
      family C hcof hfib p =
    (NerveProductParameter.projection (ResolutionArrowComparisonEndpoints.vertexParameter C)
      ResolutionArrowCylinderBoundary.interval.{max u v}).app ((arrowFunctor C).obj p) ≫
        (ResolutionArrowComparisonEndpoints.vertexBoundary C).app ((arrowFunctor C).obj p) :=
  (UniverseLift.fixedHomotopyMap_relative.{u} (oldHomotopy C hcof hfib p)).trans
    (congrArg (fun k => fst _ _ ≫ k) (ResolutionMixedTriangles.vertexBoundary_lifted C hcof p).symm)

lemma fit : (ResolutionArrowCylinderBoundary.inclusion C).app ((arrowFunctor C).obj p) ≫
    family C hcof hfib p = NerveMovingParameter.evaluate
      (ResolutionArrowCylinderBoundary.boundaryParameter C)
      (ResolutionArrowComparisonEndpoints.values C) (ResolutionArrowCylinderBoundary.system C hcof)
        ((arrowFunctor C).obj p) :=
  ResolutionArrowCylinderFamilyFit.pointwise_fit C hcof _ _
    (zero C hcof hfib p) (one C hcof hfib p) (vertex C hcof hfib p)

lemma recover : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor (family C hcof hfib p) =
    RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
      (ResolutionMixedTriangles.oldBoundary C p) (ResolutionMixedTriangles.oldDiagonal C hcof hfib
        p) :=
  UniverseLift.fixedHomotopyMap_recover (oldHomotopy C hcof hfib p)

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedDiagonalData
