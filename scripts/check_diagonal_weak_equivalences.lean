import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u t
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.BisimplicialModel
open SerrePositivity.HomotopyFunctionComplex

-- Full boundary-index equivalence for a general Reedy structure.
example {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
    [inverse.IsMultiplicative] [direct.IsMultiplicative]
    {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
    (r : ReedyStructure inverse direct α) (j : J) :
    MatchingIndex r.op (Opposite.op j) ≌ (LatchingIndex r j)ᵒᵖ := matchingOpEquivalence r j

-- Actual matching objects and actual relative arrows, without a model hypothesis.
example (Z : SSet.{v}) (n : ℕ) :
    (ihom (SSet.boundary.{v} n).toSSet).obj Z ≅
      (matchingEvaluation simplexOp (Opposite.op (SimplexCategory.mk n))).obj
        (internalHomRight.obj Z) := matchingBoundaryIso Z n

example {Z Y : SSet.{v}} (p : Z ⟶ Y) (n : ℕ) :
    Arrow.mk (relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
      (internalHomRight.map p)) ≅ Arrow.mk (boundaryPullbackHom p n).π :=
  relativeMatchingArrowIso p n

-- The Quillen condition is now proved from the original value-model classes.
-- No assumed diagonal Quillen class or cofibrancy of B and B' is supplied.
example [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : B ⟶ B')
    (hf : ∀ n, weakEquivalences SSet.{v} (f.app n)) :
    weakEquivalences SSet.{v} (DiagonalFrame.map f) :=
  diagonal_map_weakEquivalence hcof hfib f hf

-- This closes the exact comparison used by the higher lift action on any
-- model source, with no functorial factorization, generation, or enrichment.
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (X : ResolutionObject C) (Z : C) [IsFibrant Z] :
    weakEquivalences SSet.{v} (ResolutionLiftAction.comparison X Z) :=
  DiagonalMappingComparison.liftAction_comparison_weakEquivalence hcof hfib X Z

-- In particular the arbitrary-source action and its comparison coexist without
-- assuming diagonal source cofibrancy or source functorial resolution choices.
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C) [IsFibrant Z] :
    Nonempty (ResolutionLiftSpace.obj X Y f ⨯ (cosimplicialHom Y.resolution.obj).obj Z ⟶
      ResolutionLiftAction.target X Z) ∧
      weakEquivalences SSet.{v} (ResolutionLiftAction.comparison X Z) :=
  ⟨⟨ResolutionLiftAction.action X Y f Z⟩,
    DiagonalMappingComparison.liftAction_comparison_weakEquivalence hcof hfib X Z⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.IndexOppositeEquivalence,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryHom,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalMatching,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalRelativeMatching,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalQuillen,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingWeakEquivalence]
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
  unless modules.size == expected.size do throwError "Some diagonal weak equivalence modules were not audited"
  logInfo m!"Diagonal weak equivalence audit passed: {count} declarations in {modules.size} modules, standard axioms only."
