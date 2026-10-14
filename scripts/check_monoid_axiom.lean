import SerrePositivity.HomotopicalAlgebra.Monoidal.MonoidAxiom
import Lean.Util.CollectAxioms

universe w u v
open CategoryTheory HomotopicalAlgebra SerrePositivity.Quillen
open CategoryTheory.MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [ModelCategory C]
  [HasMonoidAxiom.{w} C]

-- The tensor parameter need not be cofibrant.
example {A B : C} (f : A ⟶ B) [Cofibration f] [WeakEquivalence f] (X : C) :
    WeakEquivalence (f ▷ X) := tensor_trivialCofibration_weakEquivalence f X

example (J : MorphismProperty C) (hJ : J ≤ trivialCofibrations C) :
    (relativeCells.{w} (tensorRightImages J)).retracts ≤ weakEquivalences C :=
  tensorCells_retracts_le_weakEquivalences J hJ

example (J : MorphismProperty C) (hJ : J ≤ trivialCofibrations C)
    [(tensorRightImages J).HasSmallObjectArgument.{w}] :
    (tensorRightImages J).rlp.llp ≤ weakEquivalences C :=
  tensorGenerated_le_weakEquivalences J hJ

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Monoidal.MonoidAxiom do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No monoid axiom declarations audited"
  logInfo m!"Monoid axiom audit passed: {count} declarations, standard axioms only."
