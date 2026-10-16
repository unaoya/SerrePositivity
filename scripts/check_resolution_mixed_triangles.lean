import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w uD vD v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open NerveCylinderBoundary NerveBiparameterMaps

section GeneralVertexBoundary
variable {D : Type uD} [Category.{vD} D] (K F V : D ⥤ SSet.{w}) {n : ℕ}
  (faces : Fin (n + 3) → NerveBiparameter.System
    (product K (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))) F)
  (hf : NerveMovingBoundary.Compatible K F faces) (i : V ⟶ K) (b : V ⟶ F)
  (hv : ∀ k : Fin (n + 3), faces k ≫ restriction _ _ F
    (horizontal V K i (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))) =
    NerveNaturalBoundary.ofNatTrans _ _ (NerveProductParameter.projection V
      (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1))) ≫ b))
-- Moving-index gluing preserves the entire vertex boundary without a model structure.
example : NerveMovingBoundary.boundary K F faces hf ≫ restriction _ _ F
    (horizontal V K i (SSet.boundary (n + 2)).toSSet) =
    NerveNaturalBoundary.ofNatTrans _ _
      (NerveProductParameter.projection V (SSet.boundary (n + 2)).toSSet ≫ b) :=
  NerveMovingBoundary.boundary_vertices K F faces hf V i b hv
end GeneralVertexBoundary

section ActualWholeMixedTriangles
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
open ResolutionMixedDiagram ResolutionMixedCoherentTriangles

-- All five old entire facet systems have the same full vertex restriction.
example (side : Bool) (k : Fin 3) : ResolutionMixedFaceSystems.faces C hcof hfib side k ≫
    restriction _ _ (NerveMovingParameter.lifted (smallValues C))
      (ResolutionMixedVertexRestrictions.vertexMap C) =
    ResolutionMixedVertexRestrictions.fixedVertices C :=
  ResolutionMixedVertexRestrictions.faces_vertices C hcof hfib side k

-- The actual original whole triangles fit the actual Q₂ pushout.
example (side : Bool) (p : Index C) : (ResolutionMixedTriangleBoundary.inclusion C).app p ≫
    ResolutionMixedTriangles.triangle C hcof hfib p side =
    NerveMovingParameter.evaluate (ResolutionMixedTriangleBoundary.boundaryParameter C)
      (smallValues C) (ResolutionMixedTriangleBoundary.system C hcof hfib side) p :=
  ResolutionMixedTriangleBoundary.triangle_fit C hcof hfib side p

-- No new lower-dimensional compatibility assumption is required for this extension.
example (side : Bool) : coherent C hcof hfib side ≫ restriction _ _
    (NerveMovingParameter.lifted (smallValues C)) (ResolutionMixedTriangleBoundary.inclusion C) =
    ResolutionMixedTriangleBoundary.system C hcof hfib side := coherent_boundary C hcof hfib side
example (side : Bool) (k : Fin 3) : coherent C hcof hfib side ≫ restriction _ _
    (NerveMovingParameter.lifted (smallValues C))
    (vertical (SSet.stdSimplex.δ k) (parameters C)) =
    ResolutionMixedFaceSystems.faces C hcof hfib side k := coherent_face C hcof hfib side k
example (side : Bool) : coherent C hcof hfib side ≫ restriction _ _
    (NerveMovingParameter.lifted (smallValues C))
    (horizontal (vertexParameters C) (parameters C) (ResolutionMixedDiagram.vertexInclusion C)
      (SSet.stdSimplex.obj (SimplexCategory.mk 2))) =
    ResolutionMixedTriangleBoundary.vertices C := coherent_vertices C hcof hfib side
example : coherent C hcof hfib true ≫ restriction _ _
    (NerveMovingParameter.lifted (smallValues C))
    (vertical (SSet.stdSimplex.δ (1 : Fin 3)) (parameters C)) =
    coherent C hcof hfib false ≫ restriction _ _
      (NerveMovingParameter.lifted (smallValues C))
      (vertical (SSet.stdSimplex.δ (1 : Fin 3)) (parameters C)) := shared_diagonal C hcof hfib

-- Each entire original small triangle, including every tuple and triangle degree, is recovered.
example (side : Bool) (p : Index C) : UniverseLift.lowerSimplexTensor
    (NerveMovingParameter.evaluate (ResolutionMixedBoundary.fullParameter C) (smallValues C)
      (coherent C hcof hfib side) p) =
    RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
      (ResolutionMixedTriangles.oldBoundary C p)
      (ResolutionMixedTriangles.oldTriangle C hcof hfib p side) :=
  coherent_recover C hcof hfib side p
end ActualWholeMixedTriangles

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveMovingBoundary,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveNaturalBoundaryTransport,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalVertices,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do
    throwError "Some whole mixed triangle modules were not audited"
  logInfo m!"Whole mixed triangle audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
