import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u uD vD uE vE w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionArrowComparisonEndpoints

section GenericCanonicalBoundary
-- No model structure and independent source/reindexing object and Hom universes.
variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  (V K F : D ⥤ SSet.{w}) (i : V ⟶ K) (b : V ⟶ F)
  (a : NerveBiparameter.System K F)
  (ha : a ≫ NerveBiparameterMaps.restriction V K F i =
    NerveNaturalBoundary.ofNatTrans V F b) (H : E ⥤ Arrow D)

example : NerveBiparameter.System (H ⋙ NerveArrowComparison.source K)
    (H ⋙ NerveArrowComparison.target F) :=
  NerveBiparameterMaps.reindex _ _ H (NerveArrowComparison.left K F a)

example : NerveArrowComparison.left K F a ≫ NerveBiparameterMaps.restriction
    (NerveArrowComparison.source V) (NerveArrowComparison.source K)
      (NerveArrowComparison.target F) (NerveArrowComparison.sourceMap i) =
    NerveArrowComparison.right K F a ≫ NerveBiparameterMaps.restriction
      (NerveArrowComparison.source V) (NerveArrowComparison.source K)
        (NerveArrowComparison.target F) (NerveArrowComparison.sourceMap i) :=
  (NerveArrowComparison.left_boundary V K F i b a ha).trans
    (NerveArrowComparison.right_boundary V K F i b a ha).symm
end GenericCanonicalBoundary

section ActualSmallEndpoints
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
open ResolutionArrowDiagram ResolutionArrowElementary

-- Entire all-center endpoint systems have the same canonical whole strict-vertex boundary.
example : left C hcof ≫ NerveBiparameterMaps.restriction
    (vertexParameter C) (parameter C) (NerveMovingParameter.lifted (values C))
      (vertexInclusion C) = right C hcof ≫ NerveBiparameterMaps.restriction
        (vertexParameter C) (parameter C) (NerveMovingParameter.lifted (values C))
          (vertexInclusion C) := (left_vertices C hcof).trans (right_vertices C hcof).symm

-- These are the old full small maps, including every higher ordered tuple simplex.
example (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) : UniverseLift.lower
    (NerveMovingParameter.evaluate (parameter C) (values C)
      (left C hcof) (Arrow.mk (post X Y W f g))) =
    CoherentLiftRelative.postLeft hcof X.inner Y W f g := post_left hcof X Y W f g

example (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) : UniverseLift.lower
    (NerveMovingParameter.evaluate (parameter C) (values C)
      (right C hcof) (Arrow.mk (post X Y W f g))) =
    CoherentLiftRelative.postRight hcof X.inner Y W f g := post_right hcof X Y W f g

-- An arbitrary actual frame map is used, with no chosen functorial source factorization.
example (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) : UniverseLift.lower
    (NerveMovingParameter.evaluate (parameter C) (values C)
      (left C hcof) (Arrow.mk (pre X Y W f g))) =
    CoherentLiftRelative.preLeft hcof X.inner Y.inner W f.map g (FramedResolution.frameMap f) :=
  pre_left hcof X Y W f g

example (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) : UniverseLift.lower
    (NerveMovingParameter.evaluate (parameter C) (values C)
      (right C hcof) (Arrow.mk (pre X Y W f g))) =
    CoherentLiftRelative.preRight hcof X.inner Y.inner W f.map g := pre_right hcof X Y W f g

-- All external faces and degeneracies still use actual first and last transports.
example {s t : NerveSimplexEndpoint.Index (Arrow (Index C))} (f : s ⟶ t) :
    SSet.stdSimplex.map (NerveSimplexEndpoint.operator f) ≫ (left C hcof).app t =
    (left C hcof).app s ≫
      (CategoryTheory.MonoidalClosed.pre ((parameter C).map (NerveSimplexStart.startMap f))).app
        (UniverseLift.obj.{u} ((values C).obj (NerveSimplexEndpoint.endpoint s))) ≫
      (ihom ((parameter C).obj (NerveSimplexStart.start t))).map
        (UniverseLift.map.{u} ((values C).map (NerveSimplexEndpoint.endpointMap f))) :=
  NerveBiparameter.compatibility _ _ _ f
end ActualSmallEndpoints

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBiparameterMapLaws,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBiparameterEvaluation,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveArrowComparison,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowElementary]
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
    throwError "Some actual all-center comparison endpoint modules were not audited"
  logInfo m!"Actual comparison endpoints audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
