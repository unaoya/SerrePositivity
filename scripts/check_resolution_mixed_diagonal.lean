import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedIntervalRestrictions

section WholeMixedDiagonal
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
open ResolutionMixedCoherentDiagonal ResolutionMixedEndpointCompatibility

-- The entire selected small diagonal, not merely its vertices, is recovered.
example (p : Index C) : UniverseLift.lowerSimplexTensor
    (NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
      (coherent C hcof hfib) p) =
    RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
      (ResolutionMixedTriangles.oldBoundary C p)
      (ResolutionMixedTriangles.oldDiagonal C hcof hfib p) := coherent_recover C hcof hfib p

-- The very same full Q-boundary is held fixed in every external degree.
example : coherent C hcof hfib ≫ NerveBiparameterMaps.restriction (boundaryParameters C)
    (intervalParameters C) (NerveMovingParameter.lifted (smallValues C)) (boundaryInclusion C) =
      fixedBoundary C hcof := coherent_boundary C hcof hfib
example : coherent C hcof hfib ≫ NerveBiparameterMaps.restriction
    (NerveCylinderBoundary.product (vertexParameters C)
      ResolutionArrowCylinderBoundary.interval.{max u v})
    (intervalParameters C) (NerveMovingParameter.lifted (smallValues C))
    (NerveCylinderBoundary.horizontal (vertexParameters C) (parameters C)
      (ResolutionMixedDiagram.vertexInclusion C)
      ResolutionArrowCylinderBoundary.interval.{max u v}) =
    NerveNaturalBoundary.ofNatTrans _ _
      (NerveProductParameter.projection (vertexParameters C)
        ResolutionArrowCylinderBoundary.interval.{max u v} ≫
          ResolutionMixedDiagram.vertexBoundary C) := coherent_vertices C hcof hfib
example : endpoint C (coherent C hcof hfib) 1 = expand C (corner0 C hcof) :=
  coherent_zero C hcof hfib
example : endpoint C (coherent C hcof hfib) 0 = expand C (corner3 C hcof) :=
  coherent_one C hcof hfib

-- The same five whole systems satisfy all boundary compatibility identities.
example (side : Bool) (j k : Fin 3) (hjk : j < k) :
    endpoint C (ResolutionMixedFaceSystems.faces C hcof hfib side j)
      (k.pred (Fin.ne_zero_of_lt hjk)) =
    endpoint C (ResolutionMixedFaceSystems.faces C hcof hfib side k)
      (j.castPred (Fin.ne_last_of_lt hjk)) :=
  ResolutionMixedFaceSystems.compatible C hcof hfib side j k hjk
example : ResolutionMixedFaceSystems.faces C hcof hfib true 1 =
    ResolutionMixedFaceSystems.faces C hcof hfib false 1 :=
  ResolutionMixedFaceSystems.shared_diagonal C hcof hfib

-- Every face of each original entire triangle evaluates to that fixed whole edge system.
example (side : Bool) (k : Fin 3) (p : Index C) :
    (parameters C).obj p ◁ SSet.stdSimplex.δ k ≫
      ResolutionMixedTriangles.triangle C hcof hfib p side =
    NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
      (ResolutionMixedFaceSystems.faces C hcof hfib side k) p :=
  ResolutionMixedFaceSystems.old_triangle_faces C hcof hfib side k p
example (side : Bool) (k : Fin 3) (p : Index C) : UniverseLift.lowerSimplexTensor
    (NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
      (ResolutionMixedFaceSystems.faces C hcof hfib side k) p) =
    RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
      (ResolutionMixedTriangles.oldBoundary C p)
      (ResolutionMixedTriangles.oldFace C hcof hfib p side k) :=
  ResolutionMixedFaceSystems.faces_recover C hcof hfib side k p
end WholeMixedDiagonal

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedFaceSystems]
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
    throwError "Some mixed diagonal modules were not audited"
  logInfo m!"Whole mixed diagonal audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
