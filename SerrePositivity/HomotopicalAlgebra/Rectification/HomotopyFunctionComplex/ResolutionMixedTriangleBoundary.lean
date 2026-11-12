module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedBoundary
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions

/-!
# 中断した任意モデル源への一般化：ResolutionMixedTriangleBoundary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The entire facet and vertex boundary of each original mixed triangle。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0327][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0327
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The entire facet and vertex boundary of each original mixed triangle
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram NerveCylinderBoundary NerveBiparameterMaps

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev vertexParameter := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (vertexParameters C)
  (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2))
abbrev vertices := NerveNaturalBoundary.ofNatTrans (vertexParameter C)
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
  (NerveProductParameter.projection (vertexParameters C)
    (SSet.stdSimplex.obj (SimplexCategory.mk 2)) ≫ vertexBoundary C)
abbrev boundaryParameter := boundary (vertexParameters C) (parameters C)
  (ResolutionMixedDiagram.vertexInclusion C) (SSet.boundary.{max u v} 2).ι
abbrev inclusion : boundaryParameter C ⟶ ResolutionMixedBoundary.fullParameter C :=
  NerveCylinderBoundary.inclusion (vertexParameters C) (parameters C)
    (ResolutionMixedDiagram.vertexInclusion C) (SSet.boundary 2).ι
abbrev facetsInclusion : ResolutionMixedBoundary.boundaryParameter C ⟶ boundaryParameter C :=
  endpointInclusion (vertexParameters C) (parameters C)
    (ResolutionMixedDiagram.vertexInclusion C) (SSet.boundary 2).ι
abbrev verticesInclusion : vertexParameter C ⟶ boundaryParameter C :=
  NerveCylinderBoundary.vertexInclusion (vertexParameters C) (parameters C)
    (ResolutionMixedDiagram.vertexInclusion C) (SSet.boundary 2).ι

lemma compatible (side : Bool) : ResolutionMixedBoundary.system C hcof hfib side ≫
    restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (vertexParameters C) (parameters C) (ResolutionMixedDiagram.vertexInclusion C)
        (SSet.boundary 2).toSSet) = vertices C ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.boundary 2).ι (vertexParameters C)) := by
  apply (NerveMovingBoundary.boundary_vertices (parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (ResolutionMixedFaceSystems.faces C hcof hfib side)
    (ResolutionMixedFaceSystems.compatible C hcof hfib side)
    (vertexParameters C) (ResolutionMixedDiagram.vertexInclusion C) (vertexBoundary C)
    (ResolutionMixedVertexRestrictions.faces_vertices C hcof hfib side)).trans
  symm
  apply (restrict_natural _ _ _ _ _).trans
  apply congrArg (NerveNaturalBoundary.ofNatTrans _ _)
  rw [← Category.assoc, NerveProductParameter.projection_vertical]

/-- The actual Q₂ pushout fixes the entire triangle boundary and entire vertex cylinder. -/
def system (side : Bool) : NerveMovingParameter.System.{u, v}
    (boundaryParameter C) (smallValues C) :=
  NerveCylinderBoundary.system (vertexParameters C) (parameters C)
    (ResolutionMixedDiagram.vertexInclusion C) (SSet.boundary 2).ι
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (ResolutionMixedBoundary.system C hcof hfib side) (vertices C) (compatible C hcof hfib side)

lemma system_facets (side : Bool) : system C hcof hfib side ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (facetsInclusion C) =
    ResolutionMixedBoundary.system C hcof hfib side :=
  NerveCylinderBoundary.system_endpoints _ _ _ _ _ _ _ _

lemma system_vertices (side : Bool) : system C hcof hfib side ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (verticesInclusion C) = vertices C :=
  NerveCylinderBoundary.system_vertices _ _ _ _ _ _ _ _

omit [ModelCategory SSet.{v}] in
lemma inclusion_mono (p : Index C) : Mono ((inclusion C).app p) :=
  NerveCylinderBoundary.inclusion_mono (vertexParameters C) (parameters C)
    (ResolutionMixedDiagram.vertexInclusion C) (SSet.boundary 2).ι
    (ResolutionMixedDiagram.vertexInclusion_mono C) p

/-- The old entire triangles fit Q₂ by their actual facet and vertex equations. -/
lemma triangle_fit (side : Bool) (p : Index C) : (inclusion C).app p ≫
    ResolutionMixedTriangles.triangle C hcof hfib p side =
    NerveMovingParameter.evaluate (boundaryParameter C) (smallValues C)
      (system C hcof hfib side) p := by
  apply (NervePushoutBoundary.square
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (vertexParameters C) (SSet.boundary 2).toSSet)
    (ResolutionMixedBoundary.boundaryParameter C) (vertexParameter C)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (vertexParameters C) (parameters C) (ResolutionMixedDiagram.vertexInclusion C)
      (SSet.boundary 2).toSSet)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.boundary 2).ι (vertexParameters C)) p).hom_ext
  · have hfac := congr_app (endpointInclusion_inclusion
      (vertexParameters C) (parameters C) (ResolutionMixedDiagram.vertexInclusion C)
      (SSet.boundary 2).ι) p
    exact ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫
      ResolutionMixedTriangles.triangle C hcof hfib p side) hfac)).trans
      ((ResolutionMixedBoundary.triangle_fit C hcof hfib side p).trans
        (NerveEvaluationLaws.restriction _ _ _ _ _ _
          (system_facets C hcof hfib side) p).symm)
  · have hfac := congr_app (NerveCylinderBoundary.vertexInclusion_inclusion
      (vertexParameters C) (parameters C) (ResolutionMixedDiagram.vertexInclusion C)
      (SSet.boundary 2).ι) p
    exact ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫
      ResolutionMixedTriangles.triangle C hcof hfib p side) hfac)).trans
      ((ResolutionMixedTriangles.triangle_vertices C hcof hfib p side).trans
        ((NerveEvaluationLaws.restriction _ _ _ _ _ _
          (system_vertices C hcof hfib side) p).trans
            (NerveEvaluationLaws.natural _ _ _ p)).symm)

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary
