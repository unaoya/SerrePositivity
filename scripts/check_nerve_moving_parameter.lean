import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe w v u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.NerveSimplexEndpoint

section GeneralMovingParameters
-- K can change by arbitrary maps. Only the original small values have boundary fillers.
variable {D : Type uD} [Category.{vD} D]
  (K : D ⥤ SSet.{max w v}) (F : D ⥤ SSet.{v})
  (hp : ∀ d, UniverseLift.BoundaryFillers (F.obj d))
  (families : ∀ d, K.obj d ⟶ UniverseLift.obj.{w} (F.obj d))

example (d : D) : NerveMovingParameter.evaluate K F
    (NerveMovingParameter.extendFamilies K F hp families) d = families d :=
  NerveMovingParameter.extendFamilies_evaluate _ _ _ _ d

-- This includes the first face's actual K-map and the last face's actual F-map.
example {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ (NerveMovingParameter.extendFamilies K F hp families).app (ofChain c) =
    (NerveMovingParameter.extendFamilies K F hp families).app
      (ofChain ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
      (pre (K.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))))).app
        (UniverseLift.obj.{w} (F.obj (c.obj (θ.toOrderHom (Fin.last m))))) ≫
      (ihom (K.obj (c.obj 0))).map
        (UniverseLift.map.{w}
          (F.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))) :=
  NerveBiparameter.reindex_compatibility _ _ _ c θ

variable (L : D ⥤ SSet.{max w v}) (i : L ⟶ K) (hi : ∀ d, Mono (i.app d))
  (target : NerveMovingParameter.System L F)
  (hboundary : NerveMovingParameter.vertices K F families ≫
    Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (NerveMovingParameterRelative.restriction L K i F) =
    Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) 1) target)

-- The whole moving boundary system stays fixed in every external degree.
example : NerveMovingParameterRelative.extendFamilies L K i F hp hi target families hboundary ≫
    NerveMovingParameterRelative.restriction L K i F = target :=
  NerveMovingParameterRelative.extendFamilies_boundary _ _ _ _ _ _ _ _ _

-- All original whole families are retained at once, with that entire boundary fixed.
example (d : D) : NerveMovingParameter.evaluate K F
    (NerveMovingParameterRelative.extendFamilies L K i F hp hi target families hboundary) d =
      families d := NerveMovingParameterRelative.extendFamilies_evaluate _ _ _ _ _ _ _ _ _ d
end GeneralMovingParameters

section GeneralNerveValues
-- Arbitrary chain-dependent values are permitted; no model on SSet is supplied.
variable {D : Type uD} [Category.{vD} D] (A B : Index D ⥤ SSet.{v}) (p : A ⟶ B)
  (hA : NerveDiagramExtension.InvertsInverse A) (hB : NerveDiagramExtension.InvertsInverse B)
  (hp : ∀ s, (MorphismProperty.monomorphisms SSet.{v}).rlp (p.app s))
  (target : NerveDiagramExtension.System B) (n : ℕ) (old : NerveDiagramExtension.LowerSystem A n)
  (hboundary : old ≫ Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n) p =
    Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n) target)

example : NerveDiagramExtension.extend A B p hA hB hp target n old hboundary ≫ p = target :=
  NerveDiagramExtension.extend_boundary _ _ _ _ _ _ _ _ _ _

example : Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n)
    (NerveDiagramExtension.extend A B p hA hB hp target n old hboundary) = old :=
  NerveDiagramExtension.extend_restrict _ _ _ _ _ _ _ _ _ _
end GeneralNerveValues

section ActualMovingCenterFactorizations
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (families : ∀ q, (ResolutionArrowParameters.parameters C).obj q ⟶
    UniverseLift.obj.{u} ((ResolutionArrowDiagram.fibers C).obj q))

example (q : ResolutionArrowDiagram.Index C) :
    NerveMovingParameter.evaluate.{u, v} (ResolutionArrowParameters.parameters C)
      (ResolutionArrowDiagram.fibers C) (ResolutionArrowParameters.system C hcof families) q =
        families q := ResolutionArrowParameters.system_evaluate C hcof families q

-- Actual center maps transport factorization categories, retaining every cut and middle map.
example {q r : ResolutionArrowDiagram.Index C} (f : q ⟶ r) :
    (ResolutionArrowParameters.parameters C).map f = AnchoredChain.mapFunctor
      (ArrowContext.factorizationMap ((ResolutionArrowDiagram.baseIndex C).map f)) := rfl

-- The resulting system uses actual changing first parameters and changing last lift values.
example {s t : Index (ResolutionArrowDiagram.Index C)} (f : s ⟶ t) :
    SSet.stdSimplex.map (operator f) ≫ (ResolutionArrowParameters.system C hcof families).app t =
    (ResolutionArrowParameters.system C hcof families).app s ≫
      (pre ((ResolutionArrowParameters.parameters C).map (NerveSimplexStart.startMap f))).app
        (UniverseLift.obj.{u} ((ResolutionArrowDiagram.fibers C).obj (endpoint s))) ≫
      (ihom ((ResolutionArrowParameters.parameters C).obj (NerveSimplexStart.start t))).map
        (UniverseLift.map.{u} ((ResolutionArrowDiagram.fibers C).map (endpointMap f))) :=
  ResolutionArrowParameters.system_compatibility C hcof families f
end ActualMovingCenterFactorizations

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.NerveSimplexStart,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBiparameter,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveDiagramExtension,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveMovingParameter,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagramUniverseLift,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveMovingParameterRelative,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowParameters]
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
    throwError "Some moving parameter modules were not audited"
  logInfo m!"Moving parameter coherence audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
