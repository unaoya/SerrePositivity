import SerrePositivity.Inputs.Homotopy.ResolutionHom
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

noncomputable section
universe v u
open CategoryTheory HomotopicalAlgebra
open SerrePositivity SerrePositivity.Inputs.Homotopy
open SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- Only the source model is supplied by the consumer; HT-KQ supplies the
-- fixed value model, and the conclusion uses the realization-based class.
example (X : C) {Y Z : C} [IsFibrant Y] [IsFibrant Z] (f : Y ⟶ Z) [WeakEquivalence f] :
    SimplicialHomotopy.weakEquivalences
      ((cosimplicialHom (Reedy.cosimplicialResolution X).obj).map f) :=
  resolutionHom_target_geometricWeakEquivalence X f

example
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {X X' : Cᵒᵖ} (f : X ⟶ X') (hf : weakEquivalences C f.unop)
    {Y Y' : C} (g : Y ⟶ Y') (hg : weakEquivalences C g) :
    SimplicialHomotopy.weakEquivalences
      (((chosenResolutionHom cof fib).map f).app Y ≫
        ((chosenResolutionHom cof fib).obj X').map g) :=
  chosenResolutionHom_geometricWeakEquivalence cof fib f hf g hg

open Lean in
run_cmd do
  let env ← getEnv
  let mut directInputs : Array Name := #[]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless #[`SerrePositivity.Inputs.Homotopy.KanQuillen,
        `SerrePositivity.Inputs.Homotopy.ResolutionHom,
        `SerrePositivity.HomotopicalAlgebra.Simplicial.WeakEquivalence,
        `SerrePositivity.HomotopicalAlgebra.Topological.WeakEquivalence,
        `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TargetInvariance,
        `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SourceInvariance,
        `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PresentationSourceLifting,
        `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.RelativeBoundaryTensor].contains mod do continue
    if (info.value? true).any (·.hasSorry) then directInputs := directInputs.push name
    let axioms ← collectAxioms name
    let allowed := if (`SerrePositivity.Inputs.Homotopy).isPrefixOf mod then
        #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
      else #[``propext, ``Classical.choice, ``Quot.sound]
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  unless directInputs == #[``kanQuillen_model_exists] do
    throwError "Expected exactly HT-KQ as the direct literature input, got {directInputs}"
  logInfo m!"Kan–Quillen resolution Hom audit passed: {count} declarations; sole direct citation HT-KQ."
