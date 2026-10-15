import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
import Lean.Util.CollectAxioms

universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy Simplicial

variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) {C : Type u'} [Category.{v'} C]

example {j : J} (f : LatchingIndex r j) : r.deg f.obj.left < r.deg j := latching_degree_lt r f
example {j : J} (f : MatchingIndex r j) : r.deg f.obj.right < r.deg j := matching_degree_lt r f

example (j : J) [HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C]
    {F G : J ⥤ C} (τ : F ⟶ G) :
    pushout.inr ((latchingEvaluation r j).map τ) ((latchingComparison r j).app F) ≫
      relativeLatchingMap r j τ = τ.app j := inr_relativeLatchingMap r j τ

example (j : J) [HasLimitsOfShape (MatchingIndex r j) C] [HasPullbacks C]
    {F G : J ⥤ C} (τ : F ⟶ G) :
    relativeMatchingMap r j τ ≫
      pullback.fst ((matchingComparison r j).app G) ((matchingEvaluation r j).map τ) = τ.app j :=
  relativeMatchingMap_fst r j τ

example : IsEmpty (LatchingIndex simplex ⦋0⦌) := latching_isEmpty_of_isMin simplex isMin_bot
example : IsEmpty (MatchingIndex simplex ⦋0⦌) := matching_isEmpty_of_isMin simplex isMin_bot
example : IsEmpty (LatchingIndex simplexOp (Opposite.op ⦋0⦌)) :=
  latching_isEmpty_of_isMin simplexOp isMin_bot

example {i j : SimplexCategory} (f : i ⟶ j) :
    (simplex.mapFactorizationData f).i ≫ (simplex.mapFactorizationData f).p = f :=
  (simplex.mapFactorizationData f).fac

example {i j : SimplexCategory} (f : i ⟶ j)
    (d : MorphismProperty.MapFactorizationData simplexInverse simplexDirect f) :
    d = simplexFactorization f := simplexFactorization_unique f d

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex]
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
  if modules.size != expected.size then throwError "Not all Reedy object modules were audited"
  logInfo m!"Reedy object audit passed: {count} declarations in 3 modules, standard axioms only."
