import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexFinite
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

variable {C : Type u} [Category.{v} C]

example (j : SimplexCategory) : FinCategory (LatchingIndex simplex j) := inferInstance
example (j : SimplexCategory) : FinCategory (MatchingIndex simplex j) := inferInstance
example (j : SimplexCategoryᵒᵖ) : FinCategory (LatchingIndex simplexOp j) := inferInstance
example (j : SimplexCategoryᵒᵖ) : FinCategory (MatchingIndex simplexOp j) := inferInstance

-- Arbitrary model sources have precisely the finite limits and colimits needed here.
example [ModelCategory C] (j : SimplexCategory) (F : SimplexCategory ⥤ C) :
    (latchingEvaluation simplex j).obj F ⟶ F.obj j := (latchingComparison simplex j).app F

example [ModelCategory C] (j : SimplexCategory) (F : SimplexCategory ⥤ C) :
    F.obj j ⟶ (matchingEvaluation simplex j).obj F := (matchingComparison simplex j).app F

example [ModelCategory C] (j : SimplexCategoryᵒᵖ) (F : SimplexCategoryᵒᵖ ⥤ C) :
    (latchingEvaluation simplexOp j).obj F ⟶ F.obj j := (latchingComparison simplexOp j).app F

example [ModelCategory C] (j : SimplexCategoryᵒᵖ) (F : SimplexCategoryᵒᵖ ⥤ C) :
    F.obj j ⟶ (matchingEvaluation simplexOp j).obj F := (matchingComparison simplexOp j).app F

example [ModelCategory C] (j : SimplexCategoryᵒᵖ) {F G : SimplexCategoryᵒᵖ ⥤ C} (τ : F ⟶ G) :
    pushout.inr ((latchingEvaluation simplexOp j).map τ) ((latchingComparison simplexOp j).app F) ≫
      relativeLatchingMap simplexOp j τ = τ.app j := inr_relativeLatchingMap simplexOp j τ

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.IndexOpposite,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexFinite]
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
  if modules.size != expected.size then throwError "Not all finite Reedy index modules were audited"
  logInfo m!"Finite Reedy index audit passed: {count} declarations in 2 modules, standard axioms only."
