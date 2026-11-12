module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowElementary
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowCylinderFaces
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowCylinderFamilyFit
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftEdges
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.UniverseLiftFixedHomotopy

/-!
# 中断した任意モデル源への一般化：ResolutionArrowSelectedIntervals

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The already selected pre/post intervals satisfy the actual whole cylinder boundary。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0285][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0285
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The already selected pre/post intervals satisfy the actual whole cylinder boundary
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open HomotopicalAlgebra SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionArrowDiagram ResolutionArrowElementary ResolutionArrowComparisonEndpoints
open ResolutionArrowCylinderBoundary

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

omit [ModelCategory SSet.{v}] in
lemma vertex_lifted (e : Arrow (Index C)) : (vertexBoundary C).app e =
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} ((ResolutionArrowTuples.vertexData C).app e.left ≫
      (fibers C).map e.hom) := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_comp _ _).symm

abbrev postHomotopy (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) :=
  RelativeChoiceSpace.FixedBoundaryHomotopy.ofEdge (CoherentLiftRelative.vertexInclusion X.inner
    Y f)
    (CoherentLiftRelative.postBoundary X.inner Y W f g) (CoherentLiftRelative.postLeft hcof
      X.inner Y W f g) (CoherentLiftRelative.postRight hcof X.inner Y W f g)
    (CoherentLiftRelative.postLeft_vertices hcof X.inner Y W f g)
    (CoherentLiftRelative.postRight_vertices hcof X.inner Y W f g)
    (CoherentLiftRelative.postEdge hcof hfib X.inner Y W f g)
    (CoherentLiftRelative.postEdge_at_zero hcof hfib X.inner Y W f g)
    (CoherentLiftRelative.postEdge_at_one hcof hfib X.inner Y W f g)

abbrev postFamily (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) :
    (fullParameter C).obj (Arrow.mk (post X Y W f g)) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} ((values C).obj (Arrow.mk (post X Y W f g))) :=
  UniverseLift.fixedHomotopyMap.{u} (postHomotopy hcof hfib X Y W f g)

lemma post_left_lifted (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) :
    NerveMovingParameter.evaluate (parameter C) (values C) (left C hcof)
      (Arrow.mk (post X Y W f g)) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (CoherentLiftRelative.postLeft hcof
        X.inner Y W f g) :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_lower _).symm.trans
    (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} k) (post_left hcof X Y W f g))

lemma post_right_lifted (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) :
    NerveMovingParameter.evaluate (parameter C) (values C) (right C hcof)
      (Arrow.mk (post X Y W f g)) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (CoherentLiftRelative.postRight hcof
        X.inner Y W f g) :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_lower _).symm.trans
    (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} k) (post_right hcof X Y W f g))

include hcof in
lemma post_boundary_lifted (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) :
    (vertexBoundary C).app (Arrow.mk (post X Y W f g)) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u}
      (CoherentLiftRelative.postBoundary X.inner Y W f g) := by
  have hp := CoherentLiftRelative.postLeft_vertices hcof X.inner Y W f g
  change CoherentLiftRelative.vertexInclusion X.inner Y f ≫
    (CoherentLiftTuples.interpolation hcof X.inner Y f ≫ _) = _ at hp
  rw [← Category.assoc, CoherentLiftTuples.interpolation_vertices] at hp
  exact (vertex_lifted (Arrow.mk (post X Y W f g))).trans
    (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} k)
      ((congrArg (fun k => CoherentLiftRelative.vertexData X.inner Y f ≫ k)
        (post_fibers X Y W f g)).trans hp))

lemma post_zero (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) :
    (zeroInclusion C ≫ inclusion C).app (Arrow.mk (post X Y W f g)) ≫
      postFamily hcof hfib X Y W f g =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app
      (Arrow.mk (post X Y W f g)) ≫ NerveMovingParameter.evaluate (parameter C) (values C)
        (left C hcof) (Arrow.mk (post X Y W f g)) := by
  rw [ResolutionArrowCylinderFaces.zero]
  exact (UniverseLift.fixedHomotopyMap_zero.{u}
    (postHomotopy hcof hfib X Y W f g)).trans
      (congrArg (fun k => fst _ _ ≫ k) (post_left_lifted hcof X Y W f g).symm)

lemma post_one (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) :
    (oneInclusion C ≫ inclusion C).app (Arrow.mk (post X Y W f g)) ≫
      postFamily hcof hfib X Y W f g =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app
      (Arrow.mk (post X Y W f g)) ≫ NerveMovingParameter.evaluate (parameter C) (values C)
        (right C hcof) (Arrow.mk (post X Y W f g)) := by
  rw [ResolutionArrowCylinderFaces.one]
  exact (UniverseLift.fixedHomotopyMap_one.{u}
    (postHomotopy hcof hfib X Y W f g)).trans
      (congrArg (fun k => fst _ _ ≫ k) (post_right_lifted hcof X Y W f g).symm)

lemma post_vertices (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (vertexParameter C) (parameter C) (vertexInclusion C)
      interval.{max u v}).app (Arrow.mk (post X Y W f g)) ≫ postFamily hcof hfib X Y W f g =
    (NerveProductParameter.projection (vertexParameter C) interval.{max u v}).app
      (Arrow.mk (post X Y W f g)) ≫ (vertexBoundary C).app (Arrow.mk (post X Y W f g)) :=
  (UniverseLift.fixedHomotopyMap_relative.{u} (postHomotopy hcof hfib X Y W f g)).trans
    (congrArg (fun k => fst _ _ ≫ k) (post_boundary_lifted hcof X Y W f g).symm)

lemma post_fit (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) :
    (inclusion C).app (Arrow.mk (post X Y W f g)) ≫ postFamily hcof hfib X Y W f g =
    NerveMovingParameter.evaluate (boundaryParameter C) (values C) (system C hcof)
      (Arrow.mk (post X Y W f g)) :=
  ResolutionArrowCylinderFamilyFit.pointwise_fit C hcof _ _
    (post_zero hcof hfib X Y W f g) (post_one hcof hfib X Y W f g)
    (post_vertices hcof hfib X Y W f g)

/-- Recover the actual previously selected small edge family in its original coordinates. -/
lemma post_recover (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor (postFamily hcof hfib X Y W f g) =
    RelativeChoiceSpace.family (CoherentLiftRelative.vertexInclusion X.inner Y f)
      (CoherentLiftRelative.postBoundary X.inner Y W f g)
      (CoherentLiftRelative.postEdge hcof hfib X.inner Y W f g) :=
  UniverseLift.fixedHomotopyMap_recover (postHomotopy hcof hfib X Y W f g)

abbrev preHomotopy (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) :=
  RelativeChoiceSpace.FixedBoundaryHomotopy.ofEdge (CoherentLiftRelative.vertexInclusion Y.inner
    W g)
    (CoherentLiftRelative.preBoundary X.inner Y.inner W f.map g) (CoherentLiftRelative.preLeft
      hcof X.inner Y.inner W f.map g (FramedResolution.frameMap f))
      (CoherentLiftRelative.preRight hcof X.inner Y.inner W f.map g)
    (CoherentLiftRelative.preLeft_vertices hcof X.inner Y.inner W f.map g
      (FramedResolution.frameMap f))
    (CoherentLiftRelative.preRight_vertices hcof X.inner Y.inner W f.map g)
    (CoherentLiftRelative.preEdge hcof hfib X.inner Y.inner W f.map g (FramedResolution.frameMap f))
    (CoherentLiftRelative.preEdge_at_zero hcof hfib X.inner Y.inner W f.map g
      (FramedResolution.frameMap f))
    (CoherentLiftRelative.preEdge_at_one hcof hfib X.inner Y.inner W f.map g
      (FramedResolution.frameMap f))

abbrev preFamily (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) :
    (fullParameter C).obj (Arrow.mk (pre X Y W f g)) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} ((values C).obj (Arrow.mk (pre X Y W f g))) :=
  UniverseLift.fixedHomotopyMap.{u} (preHomotopy hcof hfib X Y W f g)

lemma pre_left_lifted (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) :
    NerveMovingParameter.evaluate (parameter C) (values C) (left C hcof)
      (Arrow.mk (pre X Y W f g)) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (CoherentLiftRelative.preLeft hcof
        X.inner Y.inner W f.map g (FramedResolution.frameMap f)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_lower _).symm.trans
    (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} k) (pre_left hcof X Y W f g))

lemma pre_right_lifted (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) :
    NerveMovingParameter.evaluate (parameter C) (values C) (right C hcof)
      (Arrow.mk (pre X Y W f g)) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (CoherentLiftRelative.preRight hcof
        X.inner Y.inner W f.map g) :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_lower _).symm.trans
    (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} k) (pre_right hcof X Y W f g))

include hcof in
lemma pre_boundary_lifted (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) :
    (vertexBoundary C).app (Arrow.mk (pre X Y W f g)) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u}
      (CoherentLiftRelative.preBoundary X.inner Y.inner W f.map g) := by
  have hp := CoherentLiftRelative.preLeft_vertices hcof X.inner Y.inner W f.map g
    (FramedResolution.frameMap f)
  change CoherentLiftRelative.vertexInclusion Y.inner W g ≫
    (CoherentLiftTuples.interpolation hcof Y.inner W g ≫ _) = _ at hp
  rw [← Category.assoc, CoherentLiftTuples.interpolation_vertices] at hp
  exact (vertex_lifted (Arrow.mk (pre X Y W f g))).trans
    (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} k)
      ((congrArg (fun k => CoherentLiftRelative.vertexData Y.inner W g ≫ k)
        (pre_fibers X Y W f g)).trans hp))

lemma pre_zero (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) :
    (zeroInclusion C ≫ inclusion C).app (Arrow.mk (pre X Y W f g)) ≫
      preFamily hcof hfib X Y W f g =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app
      (Arrow.mk (pre X Y W f g)) ≫ NerveMovingParameter.evaluate (parameter C) (values C)
        (left C hcof) (Arrow.mk (pre X Y W f g)) := by
  rw [ResolutionArrowCylinderFaces.zero]
  exact (UniverseLift.fixedHomotopyMap_zero.{u}
    (preHomotopy hcof hfib X Y W f g)).trans
      (congrArg (fun k => fst _ _ ≫ k) (pre_left_lifted hcof X Y W f g).symm)

lemma pre_one (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) :
    (oneInclusion C ≫ inclusion C).app (Arrow.mk (pre X Y W f g)) ≫
      preFamily hcof hfib X Y W f g =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app
      (Arrow.mk (pre X Y W f g)) ≫ NerveMovingParameter.evaluate (parameter C) (values C)
        (right C hcof) (Arrow.mk (pre X Y W f g)) := by
  rw [ResolutionArrowCylinderFaces.one]
  exact (UniverseLift.fixedHomotopyMap_one.{u}
    (preHomotopy hcof hfib X Y W f g)).trans
      (congrArg (fun k => fst _ _ ≫ k) (pre_right_lifted hcof X Y W f g).symm)

lemma pre_vertices (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (vertexParameter C) (parameter C) (vertexInclusion C)
      interval.{max u v}).app (Arrow.mk (pre X Y W f g)) ≫ preFamily hcof hfib X Y W f g =
    (NerveProductParameter.projection (vertexParameter C) interval.{max u v}).app
      (Arrow.mk (pre X Y W f g)) ≫ (vertexBoundary C).app (Arrow.mk (pre X Y W f g)) :=
  (UniverseLift.fixedHomotopyMap_relative.{u} (preHomotopy hcof hfib X Y W f g)).trans
    (congrArg (fun k => fst _ _ ≫ k) (pre_boundary_lifted hcof X Y W f g).symm)

lemma pre_fit (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) :
    (inclusion C).app (Arrow.mk (pre X Y W f g)) ≫ preFamily hcof hfib X Y W f g =
    NerveMovingParameter.evaluate (boundaryParameter C) (values C) (system C hcof)
      (Arrow.mk (pre X Y W f g)) :=
  ResolutionArrowCylinderFamilyFit.pointwise_fit C hcof _ _
    (pre_zero hcof hfib X Y W f g) (pre_one hcof hfib X Y W f g)
    (pre_vertices hcof hfib X Y W f g)

/-- Recover the actual previously selected small edge family in its original coordinates. -/
lemma pre_recover (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor (preFamily hcof hfib X Y W f g) =
    RelativeChoiceSpace.family (CoherentLiftRelative.vertexInclusion Y.inner W g)
      (CoherentLiftRelative.preBoundary X.inner Y.inner W f.map g)
      (CoherentLiftRelative.preEdge hcof hfib X.inner Y.inner W f.map g
        (FramedResolution.frameMap f)) :=
  UniverseLift.fixedHomotopyMap_recover (preHomotopy hcof hfib X Y W f g)

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals
