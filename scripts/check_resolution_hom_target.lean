import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TargetInvariance
import SerrePositivity.Spectra.ModelCategory.SimplicialWeakEquivalences
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

-- The source remains an arbitrary model category with no chosen functorial data.
example (X : C) {Y Z : C} (p : Y ⟶ Z) [Fibration p] [WeakEquivalence p] :
    trivialFibrations SSet.{v}
      ((cosimplicialHom (cosimplicialResolution X).obj).map p) :=
  cosimplicialHom_trivialFibration hcof _ (cosimplicialResolution X).cofibrant p

example (X : C) {Y Z : C} [IsFibrant Y] [IsFibrant Z] (f : Y ⟶ Z) [WeakEquivalence f] :
    weakEquivalences SSet.{v}
      ((cosimplicialHom (cosimplicialResolution X).obj).map f) :=
  cosimplicialHom_weakEquivalence_of_fibrant hcof _ (cosimplicialResolution X).cofibrant f

-- This conclusion uses the actual realization-based weak equivalences.
example (hw : weakEquivalences SSet.{v} = SerrePositivity.SimplicialHomotopy.weakEquivalences)
    (X : C) {Y Z : C} [IsFibrant Y] [IsFibrant Z] (f : Y ⟶ Z) [WeakEquivalence f] :
    SerrePositivity.SimplicialHomotopy.weakEquivalences
      ((cosimplicialHom (cosimplicialResolution X).obj).map f) :=
  cosimplicialHom_geometricWeakEquivalence_of_fibrant hcof _
    (cosimplicialResolution X).cofibrant hw f

example
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X : Cᵒᵖ) {Y Z : C} (f : Y ⟶ Z) (hf : weakEquivalences C f) :
    weakEquivalences SSet.{v} (((chosenResolutionHom cof fib).obj X).map f) :=
  chosenResolutionHom_map_target_weakEquivalence hcof cof fib X f hf

-- Compatibility is definitional, including the old named class used by HT-KQ.
example : SerrePositivity.SimplicialModelInputs.geometricWeakEquivalences.{v} =
    SerrePositivity.SimplicialHomotopy.weakEquivalences := rfl

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TargetInvariance,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.WeakEquivalence]
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
  logInfo m!"Resolution Hom target invariance audit passed: {count} declarations in {seen.size} modules."
