import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexModelCategory
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory HomotopicalAlgebra SerrePositivity.Reedy
variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- The source hypotheses are exactly ModelCategory C.
example : ModelCategory (SimplexCategory ⥤ C) := simplexModelCategory C
example : ModelCategory (SimplexCategoryᵒᵖ ⥤ C) := simplexOpModelCategory C

example {F G : SimplexCategory ⥤ C} (τ : F ⟶ G) :
    reedyRight simplex (trivialFibrations C) τ ↔
      reedyRight simplex (fibrations C) τ ∧ ∀ j, weakEquivalences C (τ.app j) :=
  reedyRight_trivialFibrations_iff simplex τ

example {F G : SimplexCategory ⥤ C} (τ : F ⟶ G) :
    reedyLeft simplex (trivialCofibrations C) τ ↔
      reedyLeft simplex (cofibrations C) τ ∧ ∀ j, weakEquivalences C (τ.app j) :=
  reedyLeft_trivialCofibrations_iff simplex τ

example {F G : SimplexCategoryᵒᵖ ⥤ C} (τ : F ⟶ G) :
    reedyRight simplexOp (trivialFibrations C) τ ↔
      reedyRight simplexOp (fibrations C) τ ∧ ∀ j, weakEquivalences C (τ.app j) :=
  reedyRight_trivialFibrations_iff simplexOp τ

example {F G : SimplexCategoryᵒᵖ ⥤ C} (τ : F ⟶ G) :
    reedyLeft simplexOp (trivialCofibrations C) τ ↔
      reedyLeft simplexOp (cofibrations C) τ ∧ ∀ j, weakEquivalences C (τ.app j) :=
  reedyLeft_trivialCofibrations_iff simplexOp τ

-- Installing the returned model exposes the declared weak equivalences.
example {F G : SimplexCategory ⥤ C} (τ : F ⟶ G)
    (hτ : ∀ j, weakEquivalences C (τ.app j)) :
    letI := simplexModelCategory C
    WeakEquivalence τ := by
  let := simplexModelCategory C
  exact ⟨hτ⟩

example {F G : SimplexCategoryᵒᵖ ⥤ C} (τ : F ⟶ G)
    (hτ : reedyRight simplexOp (fibrations C) τ) :
    letI := simplexOpModelCategory C
    Fibration τ := by
  let := simplexOpModelCategory C
  exact ⟨hτ⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ObjectwiseTrivial,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ModelCategory,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexModelCategory]
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
  logInfo m!"Reedy model-category audit passed: {count} declarations in {seen.size} modules."
