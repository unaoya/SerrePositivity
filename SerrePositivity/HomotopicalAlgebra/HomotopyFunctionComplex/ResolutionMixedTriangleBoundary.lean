module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions

/-! # The entire facet and vertex boundary of each original mixed triangle -/

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

abbrev vertexParameter := product (vertexParameters C)
  (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2))
abbrev vertices := NerveNaturalBoundary.ofNatTrans (vertexParameter C)
  (NerveMovingParameter.lifted (smallValues C))
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
    restriction _ _ (NerveMovingParameter.lifted (smallValues C))
      (horizontal (vertexParameters C) (parameters C) (ResolutionMixedDiagram.vertexInclusion C)
        (SSet.boundary 2).toSSet) = vertices C ≫ restriction _ _
    (NerveMovingParameter.lifted (smallValues C))
      (vertical (SSet.boundary 2).ι (vertexParameters C)) := by
  apply (NerveMovingBoundary.boundary_vertices (parameters C)
    (NerveMovingParameter.lifted (smallValues C))
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
    (NerveMovingParameter.lifted (smallValues C))
    (ResolutionMixedBoundary.system C hcof hfib side) (vertices C) (compatible C hcof hfib side)

lemma system_facets (side : Bool) : system C hcof hfib side ≫ restriction _ _
    (NerveMovingParameter.lifted (smallValues C)) (facetsInclusion C) =
    ResolutionMixedBoundary.system C hcof hfib side :=
  NerveCylinderBoundary.system_endpoints _ _ _ _ _ _ _ _

lemma system_vertices (side : Bool) : system C hcof hfib side ≫ restriction _ _
    (NerveMovingParameter.lifted (smallValues C)) (verticesInclusion C) = vertices C :=
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
    (product (vertexParameters C) (SSet.boundary 2).toSSet)
    (ResolutionMixedBoundary.boundaryParameter C) (vertexParameter C)
    (horizontal (vertexParameters C) (parameters C) (ResolutionMixedDiagram.vertexInclusion C)
      (SSet.boundary 2).toSSet)
    (vertical (SSet.boundary 2).ι (vertexParameters C)) p).hom_ext
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
