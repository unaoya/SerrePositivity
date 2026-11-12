module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedTriangles

/-!
# 中断した任意モデル源への一般化：ResolutionMixedEdgeRecovery

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The same four interval systems recover the four actual old mixed triangle boundary families。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0318][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0318
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The same four interval systems recover the four actual old mixed triangle boundary families
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedReassociation ResolutionMixedIntervalRestrictions
open CoherentLiftRelative CoherentLiftMixedComparison

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp) (p : Index C)

abbrev preFamily := RelativeChoiceSpace.family
  (CoherentLiftRelative.vertexInclusion p.middle.inner p.target p.center)
  (preBoundary p.source.inner p.middle.inner p.target p.pre.map p.center)
  (preEdge hcof hfib p.source.inner p.middle.inner p.target p.pre.map p.center
    (FramedResolution.frameMap p.pre))
abbrev postFamily := RelativeChoiceSpace.family
  (CoherentLiftRelative.vertexInclusion p.middle.inner p.target p.center)
  (postBoundary p.middle.inner p.target p.final p.center p.post)
  (postEdge hcof hfib p.middle.inner p.target p.final p.center p.post)
abbrev finalPreFamily := RelativeChoiceSpace.family
  (CoherentLiftRelative.vertexInclusion p.middle.inner p.final (p.center ≫ p.post.base))
  (preBoundary p.source.inner p.middle.inner p.final p.pre.map (p.center ≫ p.post.base))
  (preEdge hcof hfib p.source.inner p.middle.inner p.final p.pre.map (p.center ≫ p.post.base)
    (FramedResolution.frameMap p.pre))
abbrev finalPostFamily := RelativeChoiceSpace.family
  (CoherentLiftRelative.vertexInclusion p.source.inner p.target (p.pre.map.base ≫ p.center))
  (postBoundary p.source.inner p.target p.final (p.pre.map.base ≫ p.center) p.post)
  (postEdge hcof hfib p.source.inner p.target p.final (p.pre.map.base ≫ p.center) p.post)

lemma oldAB : RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
    (ResolutionMixedTriangles.oldBoundary C p)
    (ResolutionMixedTriangles.oldFace C hcof hfib p true 2) = preFamily C hcof hfib p ≫
    postTail p.source.inner p.middle.inner p.target p.final p.pre.map p.center p.post :=
  RelativeChoiceSpace.family_postMap _ _ _ _
    (pre_boundary_transport hcof p.source.inner p.middle.inner p.target p.final p.pre.map
      p.center p.post (FramedResolution.frameMap p.pre)) _

lemma oldAC : RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
    (ResolutionMixedTriangles.oldBoundary C p)
    (ResolutionMixedTriangles.oldFace C hcof hfib p false 2) = postFamily C hcof hfib p ≫
    preTail p.source.inner p.middle.inner p.target p.final p.pre.map p.center p.post
      (FramedResolution.frameMap p.pre) :=
  RelativeChoiceSpace.family_postMap _ _ _ _ rfl _

lemma oldCD : RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
    (ResolutionMixedTriangles.oldBoundary C p)
    (ResolutionMixedTriangles.oldFace C hcof hfib p false 0) =
    (tuplePost p.middle.inner p.target p.final p.center p.post ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ finalPreFamily C hcof hfib p :=
  RelativeChoiceSpace.family_preMap _ _ _ _ _ _
    (post_vertex_square p.middle.inner p.target p.final p.center p.post)
    (post_boundary_transport hcof p.source.inner p.middle.inner p.target p.final p.pre.map
      p.center p.post (FramedResolution.frameMap p.pre)) _

lemma oldBD : RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
    (ResolutionMixedTriangles.oldBoundary C p)
    (ResolutionMixedTriangles.oldFace C hcof hfib p true 0) =
    (tuplePre p.source.inner p.middle.inner p.target p.pre.map p.center ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ finalPostFamily C hcof hfib p ≫
    castMap p.source.inner p.middle.inner p.target p.final p.pre.map p.center p.post := by
  apply (congrArg (RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
    (ResolutionMixedTriangles.oldBoundary C p)) (Category.assoc _ _ _).symm).trans
  apply (RelativeChoiceSpace.family_preMap _ _ _ _ _ _
    (pre_vertex_square p.source.inner p.middle.inner p.target p.pre.map p.center)
    (mixed_boundary_transport hcof p.source.inner p.middle.inner p.target p.final p.pre.map
      p.center p.post (FramedResolution.frameMap p.pre)) _).trans
  exact congrArg (fun k => (tuplePre p.source.inner p.middle.inner p.target p.pre.map p.center ▷
    SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ k)
      (RelativeChoiceSpace.family_postMap _ _ _ _ rfl _)

lemma intervalAB_face : NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
    (intervalAB C hcof hfib) p = ResolutionMixedTriangles.face C hcof hfib p true 2 := by
  apply (intervalAB_evaluate C hcof hfib p).trans
  apply (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{u} (preFamily C hcof hfib p) ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} k) (bd_fibers C p)).trans
  exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_target _ _).trans
    (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{u} k) (oldAB C hcof hfib p).symm)

lemma intervalAC_face : NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
    (intervalAC C hcof hfib) p = ResolutionMixedTriangles.face C hcof hfib p false 2 := by
  apply (intervalAC_evaluate C hcof hfib p).trans
  apply (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{u} (postFamily C hcof hfib p) ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} k) (ResolutionArrowElementary.pre_fibers
      p.source p.middle p.final p.pre (p.center ≫ p.post.base))).trans
  exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_target _ _).trans
    (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{u} k) (oldAC C hcof hfib p).symm)

lemma intervalCD_face : NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
    (intervalCD C hcof hfib) p = ResolutionMixedTriangles.face C hcof hfib p false 0 := by
  apply (intervalCD_evaluate C hcof hfib p).trans
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} ((ResolutionArrowTuples.tuples C).map (ac C p)) ▷
    SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{u} (finalPreFamily C hcof hfib p) = _
  apply (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} k ▷
    SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{u} (finalPreFamily C hcof hfib p))
        (ResolutionArrowElementary.post_tuples p.middle p.target p.final p.center p.post)).trans
  exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_source _ _).trans
    (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{u} k) (oldCD C hcof hfib p).symm)

lemma intervalBD_face : NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
    (intervalBD C hcof hfib) p = ResolutionMixedTriangles.face C hcof hfib p true 0 := by
  apply (intervalBD_evaluate C hcof hfib p).trans
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} ((ResolutionArrowTuples.tuples C).map (ab C p)) ▷
    SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{u} (finalPostFamily C hcof hfib p) ≫
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (castMap p.source.inner p.middle.inner p.target p.final
          p.pre.map p.center p.post) = _
  apply (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} k ▷
    SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{u} (finalPostFamily C hcof hfib p) ≫
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (castMap p.source.inner p.middle.inner p.target p.final
          p.pre.map p.center p.post))
            (ResolutionArrowElementary.pre_tuples p.source p.middle p.target p.pre p.center)).trans
  apply (congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u}
    (tuplePre p.source.inner p.middle.inner p.target p.pre.map p.center) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ k)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_target _ _)).trans
  exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_source _ _).trans
    (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{u} k) (oldBD C hcof hfib p).symm)

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery
