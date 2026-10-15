import SerrePositivity.HomotopicalAlgebra.Localization.Detection
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory HomotopicalAlgebra SerrePositivity.Bousfield

section Simplicial
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

-- The actual quotient π₀, with no comparison to geometric realization assumed.
example {X Y : SSet.{v}} (p : X ⟶ Y) [Fibration p] [WeakEquivalence p] :
    Function.Bijective (SSet.mapπ₀ p) :=
  SerrePositivity.SimplicialModel.piZero_bijective_of_trivialFibration hcof p

example {X Y : SSet.{v}} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) [WeakEquivalence f] :
    Function.Bijective (SSet.mapπ₀ f) :=
  SerrePositivity.SimplicialModel.piZero_bijective_of_weakEquivalence_of_fibrant hcof f
end Simplicial

variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- The caller supplies the actual mapping tests, not a conservativity hypothesis.
example {X Y : C} (f : X ⟶ Y) (hf : ∀ Z, mappingTest cof fib Z f) :
    weakEquivalences C f := weakEquivalence_of_mappingTests cof fib hcof hfib f hf

example {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔ ∀ Z, mappingTest cof fib Z f :=
  weakEquivalences_iff_mappingTests cof fib hcof hfib f

example : localEquivalences cof fib ⊥ = weakEquivalences C :=
  localEquivalences_bot cof fib hcof hfib

-- Recovery covers every class consisting of original weak equivalences.
example (S : MorphismProperty C) (hS : S ≤ weakEquivalences C) :
    localEquivalences cof fib S = weakEquivalences C :=
  localEquivalences_eq_weakEquivalences_of_le cof fib hcof hfib hS

example (S : MorphismProperty C) (hS : S ≤ weakEquivalences C) (Y : C) :
    localFibrantObjects cof fib S Y ↔ IsFibrant Y :=
  localFibrantObjects_iff_of_le cof fib hcof hS Y

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Localization.Detection,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroWeakEquivalence]
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
  logInfo m!"Bousfield detection audit passed: {count} declarations in {seen.size} modules."
