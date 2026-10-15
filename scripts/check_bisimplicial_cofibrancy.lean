import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.BisimplicialModel
open SerrePositivity.HomotopyFunctionComplex

-- Absolute latching comparisons are injective without any model structure.
example (X : SSet.{v}) (j : SimplexCategoryᵒᵖ) :
    Mono ((latchingComparison simplexOp j).app X) :=
  SerrePositivity.SimplicialLatching.comparison_mono X j

-- The actual presheaf latching object is monic, not an assumed splitting in SSet.
example (B : SimplexCategoryᵒᵖ ⥤ SSet.{v}) (j : SimplexCategoryᵒᵖ) :
    Mono ((latchingComparison simplexOp j).app B) := latchingComparison_mono B j

-- All bisimplicial sets, including every double-resolution mapping object,
-- are cofibrant in the actual Reedy model.
example [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (B : SimplexCategoryᵒᵖ ⥤ SSet.{v}) :
    let := simplexOpModelCategory SSet.{v}; IsCofibrant B := isCofibrant hcof B

example {C : Type u} [Category.{v} C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (A : SimplexCategory ⥤ SimplexCategory ⥤ C) (Z : C) :
    reedyLeft simplexOp (cofibrations SSet.{v}) (initial.to (DiagonalMappingRows.obj A Z)) :=
  reedyCofibrant hcof _

-- Genuine diagonal restriction and its right Kan extension adjoint.
example : diagonal.{v} ⊣ rightAdjoint.{v} := diagonalAdjunction

example [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : B ⟶ B')
    (hf : reedyLeft simplexOp (cofibrations SSet.{v}) f) :
    cofibrations SSet.{v} (DiagonalFrame.map f) :=
  diagonal_map_reedyCofibration hcof f hf

-- A reduction only: proving the remaining Quillen condition is still required.
example [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hQ : let := simplexOpModelCategory SSet.{v}; SerrePositivity.Quillen.IsLeftQuillen diagonal.{v})
    {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : B ⟶ B')
    (hf : ∀ n, weakEquivalences SSet.{v} (f.app n)) :
    weakEquivalences SSet.{v} (DiagonalFrame.map f) :=
  diagonal_map_weakEquivalence_of_isLeftQuillen hcof hQ f hf

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.LatchingDegeneracies,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.LatchingMonomorphisms,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.BisimplicialCofibrancy,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAdjunction,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalCofibrations]
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
  unless modules.size == expected.size do throwError "Some bisimplicial cofibrancy modules were not audited"
  logInfo m!"Bisimplicial cofibrancy audit passed: {count} declarations in {modules.size} modules, standard axioms only."
