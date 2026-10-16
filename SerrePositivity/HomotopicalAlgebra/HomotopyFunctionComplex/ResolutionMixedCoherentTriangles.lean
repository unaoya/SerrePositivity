module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary

/-! # Retaining the old whole mixed triangles with their same whole facet and vertex systems -/

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
    (NerveMovingParameter.lifted (smallValues C)) (ResolutionMixedTriangleBoundary.inclusion C) =
    ResolutionMixedTriangleBoundary.system C hcof hfib side :=
  NerveMovingFamilyFit.extend_boundary _ _ _ _ _ _ _ _ _

lemma coherent_recover (side : Bool) (p : Index C) : UniverseLift.lowerSimplexTensor
    (NerveMovingParameter.evaluate (ResolutionMixedBoundary.fullParameter C) (smallValues C)
      (coherent C hcof hfib side) p) =
    RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
      (ResolutionMixedTriangles.oldBoundary C p)
      (ResolutionMixedTriangles.oldTriangle C hcof hfib p side) :=
  (congrArg UniverseLift.lowerSimplexTensor (coherent_evaluate C hcof hfib side p)).trans
    (ResolutionMixedTriangles.triangle_recover C hcof hfib p side)

lemma coherent_facets (side : Bool) : coherent C hcof hfib side ≫ restriction _ _
    (NerveMovingParameter.lifted (smallValues C)) (ResolutionMixedBoundary.inclusion C) =
    ResolutionMixedBoundary.system C hcof hfib side := by
  change coherent C hcof hfib side ≫ restriction _ _
    (NerveMovingParameter.lifted (smallValues C)) (vertical (SSet.boundary 2).ι (parameters C)) = _
  rw [← endpointInclusion_inclusion (vertexParameters C) (parameters C)
    (ResolutionMixedDiagram.vertexInclusion C) (SSet.boundary 2).ι,
    ← restriction_comp, ← Category.assoc]
  exact (congrArg (fun z => z ≫ restriction _ _ (NerveMovingParameter.lifted (smallValues C))
    (ResolutionMixedTriangleBoundary.facetsInclusion C))
      (coherent_boundary C hcof hfib side)).trans
        (ResolutionMixedTriangleBoundary.system_facets C hcof hfib side)

lemma coherent_vertices (side : Bool) : coherent C hcof hfib side ≫ restriction _ _
    (NerveMovingParameter.lifted (smallValues C))
    (horizontal (vertexParameters C) (parameters C) (ResolutionMixedDiagram.vertexInclusion C)
      (SSet.stdSimplex.obj (SimplexCategory.mk 2))) =
    ResolutionMixedTriangleBoundary.vertices C := by
  rw [← NerveCylinderBoundary.vertexInclusion_inclusion (vertexParameters C) (parameters C)
    (ResolutionMixedDiagram.vertexInclusion C) (SSet.boundary 2).ι,
    ← restriction_comp, ← Category.assoc]
  exact (congrArg (fun z => z ≫ restriction _ _ (NerveMovingParameter.lifted (smallValues C))
    (ResolutionMixedTriangleBoundary.verticesInclusion C))
      (coherent_boundary C hcof hfib side)).trans
        (ResolutionMixedTriangleBoundary.system_vertices C hcof hfib side)

omit [ModelCategory SSet.{v}] in
lemma face_composite (k : Fin 3) : ResolutionMixedBoundary.faceInclusion C k ≫
    ResolutionMixedBoundary.inclusion C = vertical (SSet.stdSimplex.δ k) (parameters C) := by
  apply NatTrans.ext
  funext p
  change (parameters C).obj p ◁ SSet.boundary.ι k ≫
    (parameters C).obj p ◁ (SSet.boundary 2).ι = _
  rw [← whiskerLeft_comp, SSet.boundary.ι_ι]
  rfl

lemma coherent_face (side : Bool) (k : Fin 3) : coherent C hcof hfib side ≫ restriction _ _
    (NerveMovingParameter.lifted (smallValues C))
    (vertical (SSet.stdSimplex.δ k) (parameters C)) =
    ResolutionMixedFaceSystems.faces C hcof hfib side k := by
  rw [← face_composite C k, ← restriction_comp, ← Category.assoc,
    coherent_facets, ResolutionMixedBoundary.system_face]

lemma shared_diagonal : coherent C hcof hfib true ≫ restriction _ _
    (NerveMovingParameter.lifted (smallValues C))
    (vertical (SSet.stdSimplex.δ (1 : Fin 3)) (parameters C)) =
    coherent C hcof hfib false ≫ restriction _ _
      (NerveMovingParameter.lifted (smallValues C))
      (vertical (SSet.stdSimplex.δ (1 : Fin 3)) (parameters C)) :=
  (coherent_face C hcof hfib true 1).trans
    ((ResolutionMixedFaceSystems.shared_diagonal C hcof hfib).trans
      (coherent_face C hcof hfib false 1).symm)

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles
