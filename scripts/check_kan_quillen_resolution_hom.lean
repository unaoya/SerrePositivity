import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.ResolutionHom
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

-- A concrete natural zigzag for two independently chosen factorizations;
-- the auxiliary comparison choices are taken from the first end.
example
    (cof₁ cof₂ : MorphismProperty.FunctorialFactorizationData
      (cofibrations C) (trivialFibrations C))
    (fib₁ fib₂ : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations C) (fibrations C))
    (X : Cᵒᵖ) (Y : C) :
    SimplicialHomotopy.weakEquivalences
        (((ChosenComparison.left cof₁ cof₁ cof₂ fib₁ fib₁ fib₂).app X).app Y) ∧
      SimplicialHomotopy.weakEquivalences
        (((ChosenComparison.right cof₁ cof₁ cof₂ fib₁ fib₁ fib₂).app X).app Y) :=
  chosenResolutionHom_choices_geometricWeakEquivalences cof₁ cof₂ fib₁ fib₂ X Y

open Lean in
run_cmd do
  let env ← getEnv
  let mut directInputs : Array Name := #[]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless #[`SerrePositivity.InfinityCategories.ModelBridge.Inputs.KanQuillen,
        `SerrePositivity.InfinityCategories.ModelBridge.Inputs.ResolutionHom,
        `SerrePositivity.HomotopicalAlgebra.Simplicial.WeakEquivalence,
        `SerrePositivity.HomotopicalAlgebra.Topological.WeakEquivalence,
        `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TargetInvariance,
        `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SourceInvariance,
        `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PresentationSourceLifting,
        `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.RelativeBoundaryTensor,
        `SerrePositivity.HomotopicalAlgebra.Generated.CommonCofibrantReplacement,
        `SerrePositivity.HomotopicalAlgebra.Generated.CommonFibrantReplacement,
        `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHomNaturality,
        `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionComparison,
        `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TargetComparison,
        `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenComparison].contains mod do continue
    if (info.value? true).any (·.hasSorry) then directInputs := directInputs.push name
    let axioms ← collectAxioms name
    let allowed := if #[`SerrePositivity.InfinityCategories.ModelBridge.Inputs.KanQuillen,
        `SerrePositivity.InfinityCategories.ModelBridge.Inputs.ResolutionHom,
        `SerrePositivity.InfinityCategories.ModelBridge.Inputs.SimplicialLevel].contains mod then
        #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
      else #[``propext, ``Classical.choice, ``Quot.sound]
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  unless directInputs == #[``kanQuillen_model_exists] do
    throwError "Expected exactly HT-KQ as the direct literature input, got {directInputs}"
  logInfo m!"Kan–Quillen resolution Hom audit passed: {count} declarations; sole direct citation HT-KQ."
