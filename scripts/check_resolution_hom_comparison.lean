import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenComparison
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (cof cof₁ cof₂ : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))
  (fib fib₁ fib₂ : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations C) (fibrations C))

-- Actual natural transformations in both variables, not objectwise selected maps.
example : chosenResolutionHom cof₁ fib₁ ⟶
    ChosenComparison.middle cof cof₁ cof₂ fib fib₁ fib₂ :=
  ChosenComparison.left cof cof₁ cof₂ fib fib₁ fib₂
example : chosenResolutionHom cof₂ fib₂ ⟶
    ChosenComparison.middle cof cof₁ cof₂ fib fib₁ fib₂ :=
  ChosenComparison.right cof cof₁ cof₂ fib fib₁ fib₂
example (X : Cᵒᵖ) (Y : C) :
    SSet.KanComplex (((ChosenComparison.middle cof cof₁ cof₂ fib fib₁ fib₂).obj X).obj Y) :=
  ChosenComparison.middle_kanComplex cof cof₁ cof₂ fib fib₁ fib₂ X Y

-- The source comparison is available for arbitrary supplied resolution families,
-- including ones not constructed using either of the chosen source factors.
example (q q' : CofibrantResolutionFamily (C := C) simplex) :
    ResolutionComparison.left cof q q' ≫ q.augmentation =
      ResolutionComparison.right cof q q' ≫ q'.augmentation :=
  (ResolutionComparison.left_over cof q q').trans (ResolutionComparison.right_over cof q q').symm

example [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hw : weakEquivalences SSet.{v} = SerrePositivity.SimplicialHomotopy.weakEquivalences)
    (X : Cᵒᵖ) (Y : C) :
    SerrePositivity.SimplicialHomotopy.weakEquivalences
        (((ChosenComparison.left cof cof₁ cof₂ fib fib₁ fib₂).app X).app Y) ∧
      SerrePositivity.SimplicialHomotopy.weakEquivalences
        (((ChosenComparison.right cof cof₁ cof₂ fib fib₁ fib₂).app X).app Y) :=
  ChosenComparison.geometricWeakEquivalences cof cof₁ cof₂ fib fib₁ fib₂ hcof hw X Y

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Generated.CommonCofibrantReplacement,
    `SerrePositivity.HomotopicalAlgebra.Generated.CommonFibrantReplacement,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHomNaturality,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionComparison,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TargetComparison,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenComparison]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"Resolution Hom choice comparison audit passed: {count} declarations in {seen.size} modules."
