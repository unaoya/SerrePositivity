import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.NerveSimplexEndpoint

section NaturalMovingBoundary
-- No model structure in the larger universe, and no supplied coherent boundary/compatibility.
variable {D : Type uD} [Category.{vD} D]
  (L K : D ⥤ SSet.{max w v}) (F : D ⥤ SSet.{v}) (i : L ⟶ K)
  (b : L ⟶ NerveMovingParameter.lifted.{w} F)
  (families : ∀ d, K.obj d ⟶ UniverseLift.obj.{w} (F.obj d))
  (he : ∀ d, i.app d ≫ families d = b.app d)
  (hp : ∀ d, UniverseLift.BoundaryFillers (F.obj d)) (hi : ∀ d, Mono (i.app d))

example (d : D) : NerveMovingParameter.evaluate K F
    (NerveRelativeNaturalBoundary.extend L K F i b families he hp hi) d = families d :=
  NerveRelativeNaturalBoundary.extend_evaluate _ _ _ _ _ _ _ _ _ d

example : NerveRelativeNaturalBoundary.extend L K F i b families he hp hi ≫
    NerveMovingParameterRelative.restriction L K i F =
      NerveNaturalBoundary.ofNatTrans L (NerveMovingParameter.lifted F) b :=
  NerveRelativeNaturalBoundary.extend_boundary _ _ _ _ _ _ _ _ _
end NaturalMovingBoundary

section ActualOldTupleFamilies
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
open ResolutionArrowDiagram ResolutionArrowTuples ResolutionArrowTupleCoherence

example {q r : ResolutionArrowDiagram.Index C} (f : q ⟶ r) (k : StrictLift C q) :
    point C q k ≫ (fibers C).map f = point C r (strictMap C f k) := point_naturality C f k

-- The complete actual strict-vertex data is a natural transformation across all centers.
example {q r : ResolutionArrowDiagram.Index C} (f : q ⟶ r) :
    (vertices C).map f ≫ (vertexData C).app r = (vertexData C).app q ≫ (fibers C).map f :=
  (vertexData C).naturality f

-- The actual old interpolation is recovered as a full small map.
example (q : ResolutionArrowDiagram.Index C) : UniverseLift.lower
    (NerveMovingParameter.evaluate.{u, v} (bigTuples C) (fibers C) (system C hcof) q) =
      CoherentLiftTuples.interpolation hcof (source C q).inner (target C q) (arrow C q) :=
  interpolation_recover C hcof q

-- In particular, recovery at an old fixed center uses exactly its old tuple and old value space.
example (X : FramedResolution C) (Y : ResolutionObject C) (f : X.inner.base ⟶ Y.base) :
    UniverseLift.lower (NerveMovingParameter.evaluate.{u, v} (bigTuples C) (fibers C)
      (system C hcof) ((baseMaps C).elementsMk (Opposite.op X, Y) f)) =
        CoherentLiftTuples.interpolation hcof X.inner Y f := interpolation_recover C hcof _

-- Every ordered tuple simplex is retained, rather than selecting new individual fillers.
example (q : ResolutionArrowDiagram.Index C) {n : ℕ} (a : Fin (n + 1) → StrictLift C q) :
    VertexTuples.simplex a ≫ UniverseLift.lower
      (NerveMovingParameter.evaluate.{u, v} (bigTuples C) (fibers C) (system C hcof) q) =
    CoherentLiftTuples.simplex hcof (source C q).inner (target C q) (arrow C q) a :=
  simplex_recover C hcof q a

-- Old constant tuples retain their actual degeneracies and their original strict lift points.
example (q : ResolutionArrowDiagram.Index C) (k : StrictLift C q) (n : ℕ) :
    VertexTuples.simplex (fun _ : Fin (n + 1) => k) ≫ UniverseLift.lower
      (NerveMovingParameter.evaluate.{u, v} (bigTuples C) (fibers C) (system C hcof) q) =
    SSet.stdSimplex.map ((SimplexCategory.mk n).const (SimplexCategory.mk 0) 0) ≫
      CoherentLiftTuples.point (source C q).inner (target C q) (arrow C q) k := by
  rw [simplex_recover]
  exact CoherentLiftTuples.simplex_constant hcof _ _ _ k n

-- The entire strict-vertex boundary stays canonical in every external chain degree.
example : system C hcof ≫ NerveMovingParameterRelative.restriction
    (bigVertices C) (bigTuples C) (bigInclusion C) (fibers C) =
    NerveNaturalBoundary.ofNatTrans (bigVertices C)
      (NerveMovingParameter.lifted (fibers C)) (bigBoundary C) := vertices_fixed C hcof

example (s : Index (ResolutionArrowDiagram.Index C)) : (system C hcof).app s ≫
    (pre ((bigInclusion C).app (NerveSimplexStart.start s))).app
      (UniverseLift.obj.{u} ((fibers C).obj (endpoint s))) =
    SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name
      ((bigBoundary C).app (NerveSimplexStart.start s) ≫
        (NerveMovingParameter.lifted (fibers C)).map (NerveNaturalBoundary.whole s)) :=
  vertex_component C hcof s

-- All external faces and degeneracies use actual first-parameter and last-value transports.
example {s t : Index (ResolutionArrowDiagram.Index C)} (f : s ⟶ t) :
    SSet.stdSimplex.map (operator f) ≫ (system C hcof).app t = (system C hcof).app s ≫
      (pre ((bigTuples C).map (NerveSimplexStart.startMap f))).app
        (UniverseLift.obj.{u} ((fibers C).obj (endpoint s))) ≫
      (ihom ((bigTuples C).obj (NerveSimplexStart.start t))).map
        (UniverseLift.map.{u} ((fibers C).map (endpointMap f))) :=
  NerveBiparameter.compatibility _ _ _ f
end ActualOldTupleFamilies

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.VertexTuplesFunctor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveNaturalBoundary,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveRelativeNaturalBoundary,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence]
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
    throwError "Some actual tuple boundary modules were not audited"
  logInfo m!"Actual tuple boundary coherence audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
