import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u vE uE w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.NerveSimplexEndpoint

section ChangingCenters
variable {D : Type u} [Category.{v} D]
  {q r s : ArrowContext.Index D} (f : q ⟶ r) (g : r ⟶ s)

-- Parameter transport is one strict diagram on all central arrows.
example : (ArrowContext.parameters D).map (f ≫ g) =
    (ArrowContext.parameters D).map f ≫ (ArrowContext.parameters D).map g :=
  (ArrowContext.parameters D).map_comp f g

example {n : ℕ} (c : AnchoredChain (ArrowContext.arrow q) n) :
    (((ArrowContext.parameters D).map f).app (Opposite.op (SimplexCategory.mk n)) c).diagram =
      c.diagram := ArrowContext.parameters_diagram D f c

example {n : ℕ} (c : AnchoredChain (ArrowContext.arrow q) n) (j : Fin (n + 1)) :
    (((ArrowContext.parameters D).map f).app (Opposite.op (SimplexCategory.mk n)) c).cut j =
      (ArrowContext.factorizationMap f).obj (c.cut j) := ArrowContext.parameters_cut D f c j
end ChangingCenters

section IndependentReindexUniverses
-- Source and target categories, and the small value universe, are all independent.
variable {D : Type u} [Category.{v} D] {E : Type uE} [Category.{vE} E]
  (H : E ⥤ D) (F : D ⥤ SSet.{w}) (a : NerveCoherentFamily.System F)

example {s t : NerveSimplexEndpoint.Index E} (f : s ⟶ t) :
    endpointMap ((NerveCoherentReindex.index H).map f) = H.map (endpointMap f) :=
  NerveCoherentReindex.endpoint_map H f

example (s : NerveSimplexEndpoint.Index E) : (NerveCoherentReindex.reindex H F a).app s =
    a.app ((NerveCoherentReindex.index H).obj s) := rfl
end IndependentReindexUniverses

section ActualUniversalFibers
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
open ResolutionArrowDiagram

-- The original v-small actual lift space is the universal diagram's actual value.
example (q : ResolutionArrowDiagram.Index C) : (fibers C).obj q ≅
    ResolutionLiftSpace.obj (source C q).inner (target C q) (arrow C q) := fiberIso C q

example {q r : ResolutionArrowDiagram.Index C} (f : q ⟶ r) :
    (fibers C).map f ≫ (FiberFunctor.inclusion (rawProjection C) (basepoint C)).app r =
    (FiberFunctor.inclusion (rawProjection C) (basepoint C)).app q ≫
      MixedChoiceFunctor.rawPairs.map f.hom := map_inclusion C f

-- All independently given strict lift points are retained in one system over every center.
example (q : ResolutionArrowDiagram.Index C) :
    (selectedSystem C hcof).app (ofChain (ComposableArrows.mk₀ q)) =
      ResolutionLiftSpace.ofLift (ResolutionObject.lift (arrow C q)) :=
  selectedSystem_point C hcof q

-- All external operators, including center changes and degeneracies, act on that same system.
example {n m : ℕ} (c : ComposableArrows (ResolutionArrowDiagram.Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ (selectedSystem C hcof).app (ofChain c) =
    (selectedSystem C hcof).app (ofChain ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
      (fibers C).map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) :=
  NerveCoherentFamily.reindex_compatibility _ _ c θ

variable (X : FramedResolution C) (W : ResolutionObject C) (g : X.inner.base ⟶ W.base)

-- The original fixed-center diagram is recovered naturally, rather than point by point alone.
example : fromContext C X W g ⋙ fibers C ≅ MixedChoiceFunctor.fibers X W g :=
  fromContextIso C X W g

example {s t : MixedChoiceFunctor.Context X W} (k : s ⟶ t) :
    (fromContextIso C X W g).hom.app s ≫ (MixedChoiceFunctor.fibers X W g).map k =
    (fibers C).map ((fromContext C X W g).map k) ≫ (fromContextIso C X W g).hom.app t :=
  ((fromContextIso C X W g).hom.naturality k).symm

example (s : NerveSimplexEndpoint.Index (MixedChoiceFunctor.Context X W)) :
    (coherentContext C hcof (selectedPoint C) X W g).app s =
    (selectedSystem C hcof).app ((NerveCoherentReindex.index (fromContext C X W g)).obj s) ≫
      (fromContextIso C X W g).hom.app (endpoint s) :=
  coherentContext_component C hcof _ X W g s
end ActualUniversalFibers

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.ArrowContext,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.FiberFunctorReindex,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveCoherentReindex,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram]
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
    throwError "Some changing-center diagram modules were not audited"
  logInfo m!"Changing-center resolution diagram audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
