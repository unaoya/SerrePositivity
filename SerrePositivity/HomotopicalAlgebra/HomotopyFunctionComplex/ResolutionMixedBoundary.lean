module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedFaceSystems
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveMovingBoundary

/-! # The two actual mixed triangle boundaries made from the same five whole edge systems -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram NerveCylinderBoundary NerveBiparameterMaps

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedBoundary
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev boundaryParameter := product (parameters C) (SSet.boundary.{max u v} 2).toSSet
abbrev fullParameter := product (parameters C)
  (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2))
abbrev inclusion : boundaryParameter C ⟶ fullParameter C :=
  vertical (SSet.boundary 2).ι (parameters C)
abbrev faceInclusion (k : Fin 3) : ResolutionMixedIntervalRestrictions.intervalParameters C ⟶
    boundaryParameter C := vertical (SSet.boundary.ι k) (parameters C)

/-- Both genuine boundary systems retain the same original four edges and shared diagonal. -/
def system (side : Bool) : NerveMovingParameter.System.{u, v}
    (boundaryParameter C) (smallValues C) :=
  NerveMovingBoundary.boundary (parameters C) (NerveMovingParameter.lifted (smallValues C))
    (ResolutionMixedFaceSystems.faces C hcof hfib side)
    (ResolutionMixedFaceSystems.compatible C hcof hfib side)

lemma system_face (side : Bool) (k : Fin 3) : system C hcof hfib side ≫
    restriction _ _ (NerveMovingParameter.lifted (smallValues C)) (faceInclusion C k) =
    ResolutionMixedFaceSystems.faces C hcof hfib side k :=
  NerveMovingBoundary.boundary_face _ _ _ _ k

lemma shared_diagonal : system C hcof hfib true ≫
    restriction _ _ (NerveMovingParameter.lifted (smallValues C)) (faceInclusion C 1) =
    system C hcof hfib false ≫
      restriction _ _ (NerveMovingParameter.lifted (smallValues C)) (faceInclusion C 1) :=
  (system_face C hcof hfib true 1).trans
    ((ResolutionMixedFaceSystems.shared_diagonal C hcof hfib).trans
      (system_face C hcof hfib false 1).symm)

/-- The actual old whole triangle fits the glued boundary, not merely its three vertices. -/
lemma triangle_fit (side : Bool) (p : Index C) : (inclusion C).app p ≫
    ResolutionMixedTriangles.triangle C hcof hfib p side =
    NerveMovingParameter.evaluate (boundaryParameter C) (smallValues C)
      (system C hcof hfib side) p := by
  apply ProductBoundaryCotensor.parameter_hom_ext
  intro k
  change (parameters C).obj p ◁ SSet.boundary.ι k ≫
    (parameters C).obj p ◁ (SSet.boundary 2).ι ≫ _ = _
  rw [← whiskerLeft_comp_assoc, SSet.boundary.ι_ι]
  exact (ResolutionMixedFaceSystems.old_triangle_faces C hcof hfib side k p).trans
    (NerveEvaluationLaws.restriction (boundaryParameter C) (smallValues C) _
      (faceInclusion C k) (system C hcof hfib side)
      (ResolutionMixedFaceSystems.faces C hcof hfib side k)
      (system_face C hcof hfib side k) p).symm

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedBoundary
