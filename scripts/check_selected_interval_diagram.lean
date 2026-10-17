import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

section ExactTensorCoordinates
-- No model structure in either universe is needed for the actual coordinate round trip.
variable {K P : SSet.{v}} {n m : ℕ}
  (h : K ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ P)

example : UniverseLift.lowerSimplexTensor (UniverseLift.simplexTensorMap.{w} h) = h :=
  UniverseLift.lowerSimplexTensor_simplexTensorMap h

example (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    UniverseLift.obj.{w} K ◁ SSet.stdSimplex.map θ ≫ UniverseLift.simplexTensorMap h =
      UniverseLift.simplexTensorMap ((K ◁ SSet.stdSimplex.map θ) ≫ h) :=
  UniverseLift.simplexTensorMap_operator θ h
end ExactTensorCoordinates

section OriginalSelectedIntervals
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
open SelectedIntervalDiagram

-- The simultaneous diagram retains the actual previously chosen postEdge family as a full map.
example (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) : UniverseLift.lowerSimplexTensor
    (NerveMovingParameter.evaluate (parameters C) (smallValues C) (coherent C hcof hfib)
      (Presentation.post X Y W f g)) =
    RelativeChoiceSpace.family (CoherentLiftRelative.vertexInclusion X.inner Y f)
      (CoherentLiftRelative.postBoundary X.inner Y W f g)
      (CoherentLiftRelative.postEdge hcof hfib X.inner Y W f g) :=
  SelectedIntervalDiagram.post_recover C hcof hfib X Y W f g

-- Arbitrary actual frame maps are retained with the actual previously chosen preEdge family.
example (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) : UniverseLift.lowerSimplexTensor
    (NerveMovingParameter.evaluate (parameters C) (smallValues C) (coherent C hcof hfib)
      (Presentation.pre X Y W f g)) =
    RelativeChoiceSpace.family (CoherentLiftRelative.vertexInclusion Y.inner W g)
      (CoherentLiftRelative.preBoundary X.inner Y.inner W f.map g)
      (CoherentLiftRelative.preEdge hcof hfib X.inner Y.inner W f.map g
        (FramedResolution.frameMap f)) :=
  SelectedIntervalDiagram.pre_recover C hcof hfib X Y W f g

-- The entire original endpoint/vertex Q-system is the same restriction in every external degree.
example : coherent C hcof hfib ≫ NerveMovingParameterRelative.restriction
    (boundaries C) (parameters C) (boundaryInclusion C) (smallValues C) = fixedBoundary C hcof :=
  coherent_boundary C hcof hfib

-- All external faces and degeneracies retain actual changing first and last transports.
example {s t : NerveSimplexEndpoint.Index (Index C)} (f : s ⟶ t) :
    SSet.stdSimplex.map (NerveSimplexEndpoint.operator f) ≫ (coherent C hcof hfib).app t =
    (coherent C hcof hfib).app s ≫
      (CategoryTheory.MonoidalClosed.pre ((parameters C).map (NerveSimplexStart.startMap f))).app
        (UniverseLift.obj.{u} ((smallValues C).obj (NerveSimplexEndpoint.endpoint s))) ≫
      (CategoryTheory.ihom ((parameters C).obj (NerveSimplexStart.start t))).map
        (UniverseLift.map.{u} ((smallValues C).map (NerveSimplexEndpoint.endpointMap f))) :=
  NerveBiparameter.compatibility _ _ _ f
end OriginalSelectedIntervals

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftTensor,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.UniverseLiftFixedHomotopy,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowCylinderFaces,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.SelectedIntervalDiagram]
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
    throwError "Some actual selected interval modules were not audited"
  logInfo m!"Actual selected interval audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
