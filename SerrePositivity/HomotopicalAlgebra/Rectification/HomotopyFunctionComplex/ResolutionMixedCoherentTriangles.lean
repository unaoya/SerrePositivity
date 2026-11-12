module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary

/-!
# 中断した任意モデル源への一般化：ResolutionMixedCoherentTriangles

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Retaining the old whole mixed triangles with their same whole facet and vertex systems。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0315][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0315
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Retaining the old whole mixed triangles with their same whole facet and vertex systems
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram NerveCylinderBoundary NerveBiparameterMaps

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- The same old whole triangles, with all prescribed whole facets and vertices fixed. -/
def coherent (side : Bool) : NerveMovingParameter.System.{u, v}
    (ResolutionMixedBoundary.fullParameter C) (smallValues C) :=
  NerveMovingFamilyFit.extend (ResolutionMixedBoundary.fullParameter C) (smallValues C)
    (ResolutionMixedTriangleBoundary.boundaryParameter C)
    (ResolutionMixedTriangleBoundary.inclusion C)
    (fun p => ResolutionMixedTriangles.triangle C hcof hfib p side)
    (ResolutionMixedTriangleBoundary.system C hcof hfib side)
    (ResolutionMixedTriangleBoundary.triangle_fit C hcof hfib side)
    (fun p => ResolutionArrowDiagram.fillers C hcof (d C p))
    (ResolutionMixedTriangleBoundary.inclusion_mono C)

lemma coherent_evaluate (side : Bool) (p : Index C) :
    NerveMovingParameter.evaluate (ResolutionMixedBoundary.fullParameter C) (smallValues C)
      (coherent C hcof hfib side) p = ResolutionMixedTriangles.triangle C hcof hfib p side :=
  NerveMovingFamilyFit.extend_evaluate _ _ _ _ _ _ _ _ _ p

lemma coherent_boundary (side : Bool) : coherent C hcof hfib side ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (ResolutionMixedTriangleBoundary.inclusion C) =
    ResolutionMixedTriangleBoundary.system C hcof hfib side :=
  NerveMovingFamilyFit.extend_boundary _ _ _ _ _ _ _ _ _

lemma coherent_recover (side : Bool) (p : Index C) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor
    (NerveMovingParameter.evaluate (ResolutionMixedBoundary.fullParameter C) (smallValues C)
      (coherent C hcof hfib side) p) =
    RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
      (ResolutionMixedTriangles.oldBoundary C p)
      (ResolutionMixedTriangles.oldTriangle C hcof hfib p side) :=
  (congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor (coherent_evaluate C hcof hfib side p)).trans
    (ResolutionMixedTriangles.triangle_recover C hcof hfib p side)

lemma coherent_facets (side : Bool) : coherent C hcof hfib side ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (ResolutionMixedBoundary.inclusion C) =
    ResolutionMixedBoundary.system C hcof hfib side := by
  change coherent C hcof hfib side ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.boundary 2).ι (parameters C)) = _
  rw [← endpointInclusion_inclusion (vertexParameters C) (parameters C)
    (ResolutionMixedDiagram.vertexInclusion C) (SSet.boundary 2).ι,
    ← restriction_comp, ← Category.assoc]
  exact (congrArg (fun z => z ≫ restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (ResolutionMixedTriangleBoundary.facetsInclusion C))
      (coherent_boundary C hcof hfib side)).trans
        (ResolutionMixedTriangleBoundary.system_facets C hcof hfib side)

lemma coherent_vertices (side : Bool) : coherent C hcof hfib side ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (vertexParameters C) (parameters C) (ResolutionMixedDiagram.vertexInclusion C)
      (SSet.stdSimplex.obj (SimplexCategory.mk 2))) =
    ResolutionMixedTriangleBoundary.vertices C := by
  rw [← NerveCylinderBoundary.vertexInclusion_inclusion (vertexParameters C) (parameters C)
    (ResolutionMixedDiagram.vertexInclusion C) (SSet.boundary 2).ι,
    ← restriction_comp, ← Category.assoc]
  exact (congrArg (fun z => z ≫ restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (ResolutionMixedTriangleBoundary.verticesInclusion C))
      (coherent_boundary C hcof hfib side)).trans
        (ResolutionMixedTriangleBoundary.system_vertices C hcof hfib side)

omit [ModelCategory SSet.{v}] in
lemma face_composite (k : Fin 3) : ResolutionMixedBoundary.faceInclusion C k ≫
    ResolutionMixedBoundary.inclusion C = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ k) (parameters C) := by
  apply NatTrans.ext
  funext p
  change (parameters C).obj p ◁ SSet.boundary.ι k ≫
    (parameters C).obj p ◁ (SSet.boundary 2).ι = _
  rw [← whiskerLeft_comp, SSet.boundary.ι_ι]
  rfl

lemma coherent_face (side : Bool) (k : Fin 3) : coherent C hcof hfib side ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ k) (parameters C)) =
    ResolutionMixedFaceSystems.faces C hcof hfib side k := by
  rw [← face_composite C k, ← restriction_comp, ← Category.assoc,
    coherent_facets, ResolutionMixedBoundary.system_face]

lemma shared_diagonal : coherent C hcof hfib true ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (1 : Fin 3)) (parameters C)) =
    coherent C hcof hfib false ≫ restriction _ _
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (1 : Fin 3)) (parameters C)) :=
  (coherent_face C hcof hfib true 1).trans
    ((ResolutionMixedFaceSystems.shared_diagonal C hcof hfib).trans
      (coherent_face C hcof hfib false 1).symm)

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles
