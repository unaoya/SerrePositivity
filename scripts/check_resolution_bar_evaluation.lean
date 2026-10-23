import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u uD vD
noncomputable section
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel

-- Contravariant first-endpoint systems retain an arbitrary entire lower system.
example {D : Type uD} [Category.{vD} D] (F : Dᵒᵖ ⥤ SSet.{v})
    (hp : ∀ d, UniverseLift.BoundaryFillers (F.obj d)) (n : ℕ)
    (old : NerveFirstChoice.LowerSystem F n) :
    Functor.whiskerLeft
      (SerrePositivity.Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n)
      (NerveFirstChoice.extend F hp n old) = old :=
  NerveFirstChoice.extend_restrict F hp n old

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (ResolutionBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (ResolutionBarCenters.rightChoices R))

-- Evaluation exists without any simplicial model structure, at independent u and v.
example : ResolutionBarEvaluation.bar R ⟶
    UniverseLift.obj.{u} (MixedResolutionLiftAction.output R.1.unop.inner R.2.unop.inner) :=
  ResolutionBarEvaluation.evaluation R a b

-- Every simplex operator acts on the same actual bar and small reference output.
example {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (c : (ResolutionBarEvaluation.bar R).obj n) :
    SSet.stdSimplex.map θ.unop ≫ ResolutionBarEvaluation.simplex R a b n c =
      ResolutionBarEvaluation.simplex R a b m ((ResolutionBarEvaluation.bar R).map θ c) :=
  ResolutionBarEvaluation.simplex_operator R a b θ c

example : ResolutionBarReference.sectionMap R ≫ ResolutionBarEvaluation.evaluation R a b =
    UniverseLift.map.{u} (ResolutionBarReference.smallAction R a b) :=
  ResolutionBarReference.section_evaluation R a b

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- Actual whole systems exist, with the original lift points at every comma object.
example (d : ResolutionBarCenters.Comma R) :
    (ResolutionBarCenters.leftSystem R hcof).app
        (SerrePositivity.NerveSimplexEndpoint.ofChain (ComposableArrows.mk₀ d)) =
      ResolutionArrowDiagram.selectedPoint C (ResolutionBarCenters.center R d).1 :=
  ResolutionBarCenters.leftSystem_point R hcof d

example : ResolutionBarEvaluation.bar R ⟶
    UniverseLift.obj.{u} (BarOutput.output R) :=
  ResolutionBarEvaluation.evaluation R (ResolutionBarCenters.leftSystem R hcof)
    (ResolutionBarCenters.rightSystem R hcof)

-- The original small action is weakly equivalent even for arbitrary supplied whole systems.
example : weakEquivalences SSet.{v} (ResolutionBarReference.smallAction R a b) :=
  ResolutionBarReference.smallAction_weakEquivalence R a b hcof hfib

-- Only the original small model is used to invert the actual large composite.
example : IsIso (AnodyneHomotopy.anodyneQ.map
    (ResolutionBarReference.sectionMap R ≫ ResolutionBarEvaluation.evaluation R a b)) :=
  ResolutionBarReference.section_evaluation_isIso R a b hcof hfib

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveFirstChoice,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarCenters,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarFirstAction,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarEvaluation,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarReference]
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
    throwError "Some resolution bar evaluation modules were not audited"
  logInfo m!"Resolution bar evaluation audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
