import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.NestedMatching
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.NestedLatching
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexFinite
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryClasses
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory HomotopicalAlgebra SerrePositivity.Reedy

example (j : SimplexCategory) (g : MatchingIndex simplex j) :
    MatchingIndex simplex g.obj.right ≌ MatchingIndex (matchingReedy simplex j) g :=
  matchingNestedEquivalence simplex g

example (j : SimplexCategoryᵒᵖ) (g : MatchingIndex simplexOp j) :
    MatchingIndex simplexOp g.obj.right ≌ MatchingIndex (matchingReedy simplexOp j) g :=
  matchingNestedEquivalence simplexOp g

example (j : SimplexCategory) (g : LatchingIndex simplex j) :
    LatchingIndex simplex g.obj.left ≌ LatchingIndex (latchingReedy simplex j) g :=
  latchingNestedEquivalence simplex g

example (j : SimplexCategoryᵒᵖ) (g : LatchingIndex simplexOp j) :
    LatchingIndex simplexOp g.obj.left ≌ LatchingIndex (latchingReedy simplexOp j) g :=
  latchingNestedEquivalence simplexOp g

universe v u
open CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [ModelCategory C]

example {F G : SimplexCategory ⥤ C} (τ : F ⟶ G) (j : SimplexCategory)
    (hτ : reedyRight simplex (trivialFibrations C) τ) :
    trivialFibrations C ((matchingEvaluation simplex j).map τ) :=
  matchingEvaluation_mem_right simplex j τ (cofibrations C) (trivialFibrations C)
    (fun g ↦ hτ g.obj.right)

example {F G : SimplexCategory ⥤ C} (τ : F ⟶ G) (j : SimplexCategory)
    (hτ : reedyLeft simplex (cofibrations C) τ) :
    cofibrations C ((latchingEvaluation simplex j).map τ) :=
  latchingEvaluation_mem_left simplex j τ (cofibrations C) (trivialFibrations C)
    (fun g ↦ hτ g.obj.left)

example {F G : SimplexCategory ⥤ C} (τ : F ⟶ G) (j : SimplexCategory)
    (hτ : reedyRight simplex (fibrations C) τ) :
    fibrations C ((matchingEvaluation simplex j).map τ) :=
  matchingEvaluation_mem_right simplex j τ (trivialCofibrations C) (fibrations C)
    (fun g ↦ hτ g.obj.right)

example {F G : SimplexCategory ⥤ C} (τ : F ⟶ G) (j : SimplexCategory)
    (hτ : reedyLeft simplex (trivialCofibrations C) τ) :
    trivialCofibrations C ((latchingEvaluation simplex j).map τ) :=
  latchingEvaluation_mem_left simplex j τ (trivialCofibrations C) (fibrations C)
    (fun g ↦ hτ g.obj.left)

example {F G : SimplexCategoryᵒᵖ ⥤ C} (τ : F ⟶ G) (j : SimplexCategoryᵒᵖ)
    (hτ : reedyRight simplexOp (trivialFibrations C) τ) :
    trivialFibrations C ((matchingEvaluation simplexOp j).map τ) :=
  matchingEvaluation_mem_right simplexOp j τ (cofibrations C) (trivialFibrations C)
    (fun g ↦ hτ g.obj.right)

example {F G : SimplexCategoryᵒᵖ ⥤ C} (τ : F ⟶ G) (j : SimplexCategoryᵒᵖ)
    (hτ : reedyLeft simplexOp (cofibrations C) τ) :
    cofibrations C ((latchingEvaluation simplexOp j).map τ) :=
  latchingEvaluation_mem_left simplexOp j τ (cofibrations C) (trivialFibrations C)
    (fun g ↦ hτ g.obj.left)

example {F G : SimplexCategoryᵒᵖ ⥤ C} (τ : F ⟶ G) (j : SimplexCategoryᵒᵖ)
    (hτ : reedyRight simplexOp (fibrations C) τ) :
    fibrations C ((matchingEvaluation simplexOp j).map τ) :=
  matchingEvaluation_mem_right simplexOp j τ (trivialCofibrations C) (fibrations C)
    (fun g ↦ hτ g.obj.right)

example {F G : SimplexCategoryᵒᵖ ⥤ C} (τ : F ⟶ G) (j : SimplexCategoryᵒᵖ)
    (hτ : reedyLeft simplexOp (trivialCofibrations C) τ) :
    trivialCofibrations C ((latchingEvaluation simplexOp j).map τ) :=
  latchingEvaluation_mem_left simplexOp j τ (trivialCofibrations C) (fibrations C)
    (fun g ↦ hτ g.obj.left)

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[`SerrePositivity.CategoryTheory.CommaIdentities,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.OneSided,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.IndexReedy,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.NestedMatching,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.NestedLatching,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.MatchingRestriction,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LatchingRestriction,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.EmptyBoundary,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryLifting,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryClasses]
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
  logInfo m!"Reedy nested-boundary audit passed: {count} declarations in {seen.size} modules."
