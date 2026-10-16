import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedIntervalRestrictions

variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- Commuting actual mixed squares vary through actual cubes with independent source universes.
example : edgeAB C ≫ edgeBD C = edgeAC C ≫ edgeCD C := edge_commutes C

-- Reassociation is precisely the old small cast, not an independently selected comparison.
example (p : Index C) : (ResolutionArrowDiagram.fibers C).map
    (ResolutionMixedReassociation.finalIso C p).hom =
    CoherentLiftMixedComparison.castMap p.source.inner p.middle.inner p.target p.final
      p.pre.map p.center p.post := ResolutionMixedReassociation.fiber_cast C p

-- Both entire old triangles and their actual common diagonal are retained as prescribed maps.
example (p : Index C) (side : Bool) : UniverseLift.lowerSimplexTensor
    (ResolutionMixedTriangles.triangle C hcof hfib p side) =
    RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
      (ResolutionMixedTriangles.oldBoundary C p)
      (ResolutionMixedTriangles.oldTriangle C hcof hfib p side) :=
  ResolutionMixedTriangles.triangle_recover C hcof hfib p side

example (p : Index C) : (parameters C).obj p ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
    ResolutionMixedTriangles.triangle C hcof hfib p true =
    (parameters C).obj p ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
      ResolutionMixedTriangles.triangle C hcof hfib p false :=
  ResolutionMixedTriangles.shared_diagonal C hcof hfib p

-- Each of the four systems is obtained from the same previous selected interval system.
example (p : Index C) : NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
    (intervalAB C hcof hfib) p = ResolutionMixedTriangles.face C hcof hfib p true 2 :=
  ResolutionMixedEdgeRecovery.intervalAB_face C hcof hfib p

example (p : Index C) : NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
    (intervalAC C hcof hfib) p = ResolutionMixedTriangles.face C hcof hfib p false 2 :=
  ResolutionMixedEdgeRecovery.intervalAC_face C hcof hfib p

example (p : Index C) : NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
    (intervalCD C hcof hfib) p = ResolutionMixedTriangles.face C hcof hfib p false 0 :=
  ResolutionMixedEdgeRecovery.intervalCD_face C hcof hfib p

example (p : Index C) : NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
    (intervalBD C hcof hfib) p = ResolutionMixedTriangles.face C hcof hfib p true 0 :=
  ResolutionMixedEdgeRecovery.intervalBD_face C hcof hfib p

-- An old facet is recovered as the complete original small map, including every tuple degree.
example (p : Index C) : UniverseLift.lowerSimplexTensor
    (NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
      (intervalBD C hcof hfib) p) =
    RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
      (ResolutionMixedTriangles.oldBoundary C p)
      (ResolutionMixedTriangles.oldFace C hcof hfib p true 0) :=
  (congrArg UniverseLift.lowerSimplexTensor
    (ResolutionMixedEdgeRecovery.intervalBD_face C hcof hfib p)).trans
      (ResolutionMixedTriangles.face_recover C hcof hfib p true 0)

example {s t : NerveSimplexEndpoint.Index (Index C)} (f : s ⟶ t) :
    SSet.stdSimplex.map (NerveSimplexEndpoint.operator f) ≫ (intervalAB C hcof hfib).app t =
    (intervalAB C hcof hfib).app s ≫
      (CategoryTheory.MonoidalClosed.pre ((intervalParameters C).map
        (NerveSimplexStart.startMap f))).app
          (UniverseLift.obj.{u} ((smallValues C).obj (NerveSimplexEndpoint.endpoint s))) ≫
      (CategoryTheory.ihom ((intervalParameters C).obj (NerveSimplexStart.start t))).map
        (UniverseLift.map.{u} ((smallValues C).map (NerveSimplexEndpoint.endpointMap f))) :=
  NerveBiparameter.compatibility _ _ _ f

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftTensor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagram,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociation,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery]
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
    throwError "Some actual mixed boundary edge modules were not audited"
  logInfo m!"Actual mixed boundary edge audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
