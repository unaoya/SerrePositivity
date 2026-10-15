-- Audit every declaration belonging to the shared homotopical implementation modules.
import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[`SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction,
    `SerrePositivity.HomotopicalAlgebra.Under.ModelCategory,
    `SerrePositivity.HomotopicalAlgebra.Pointed.Basic,
    `SerrePositivity.HomotopicalAlgebra.Pointed.SmashModel,
    `SerrePositivity.CategoryTheory.MorphismProperty.UnderFactorization,
    `SerrePositivity.CategoryTheory.LiftingProperties.Under,
    `SerrePositivity.HomotopicalAlgebra.Generated.Basic,
    `SerrePositivity.HomotopicalAlgebra.Generated.Replacement,
    `SerrePositivity.HomotopicalAlgebra.Transfer.Recognition,
    `SerrePositivity.HomotopicalAlgebra.Smith.SolutionSet,
    `SerrePositivity.HomotopicalAlgebra.Smith.Smallness,
    `SerrePositivity.HomotopicalAlgebra.Smith.Completeness,
    `SerrePositivity.HomotopicalAlgebra.Smith.CoproductClosure,
    `SerrePositivity.HomotopicalAlgebra.Smith.GeneratingTrivialCofibrations,
    `SerrePositivity.HomotopicalAlgebra.Smith.Recognition,
    `SerrePositivity.HomotopicalAlgebra.Smith.Existence,
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleFactorization,
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleColimits,
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleIteration,
    `SerrePositivity.HomotopicalAlgebra.Smith.DependentCopower,
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleSquares,
    `SerrePositivity.HomotopicalAlgebra.Transfer.Right,
    `SerrePositivity.HomotopicalAlgebra.Quillen.Brown,
    `SerrePositivity.HomotopicalAlgebra.Quillen.DerivedFunctor,
    `SerrePositivity.HomotopicalAlgebra.Quillen.DerivedAdjunction,
    `SerrePositivity.HomotopicalAlgebra.Quillen.Equivalence,
    `SerrePositivity.HomotopicalAlgebra.Monoidal.QuillenBifunctor,
    `SerrePositivity.HomotopicalAlgebra.Monoidal.GeneratedBifunctor,
    `SerrePositivity.HomotopicalAlgebra.Monoidal.BifunctorTransport,
    `SerrePositivity.CategoryTheory.LiftingProperties.ParametrizedGeneration,
    `SerrePositivity.HomotopicalAlgebra.Monoidal.ModelCategory,
    `SerrePositivity.HomotopicalAlgebra.Monoidal.CofibrantTensor,
    `SerrePositivity.HomotopicalAlgebra.Monoidal.MonoidAxiom,
    `SerrePositivity.HomotopicalAlgebra.Transfer.CellMap,
    `SerrePositivity.HomotopicalAlgebra.Monoidal.ModuleTransfer,
    `SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationFamily,
    `SerrePositivity.HomotopicalAlgebra.Monoidal.ManyObjectTransfer,
    `SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationSmallness,
    `SerrePositivity.HomotopicalAlgebra.Monoidal.ManyObjectPresentability,
    `SerrePositivity.HomotopicalAlgebra.Enriched.TensorCotensor,
    `SerrePositivity.CategoryTheory.Enriched.TensorCotensor,
    `SerrePositivity.CategoryTheory.Enriched.EnrichedRepresentability]
  let mut declarations : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless #[`SerrePositivity.HomotopicalAlgebra,
        `SerrePositivity.CategoryTheory.Enriched,
        `SerrePositivity.CategoryTheory.MorphismProperty.UnderFactorization,
        `SerrePositivity.CategoryTheory.LiftingProperties.ParametrizedGeneration,
        `SerrePositivity.CategoryTheory.LiftingProperties.Under].any (·.isPrefixOf mod) do continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax ↦
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains ax)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"
    declarations := declarations + 1
    unless modules.contains mod do modules := modules.push mod
  if declarations == 0 then throwError "No homotopical foundations declarations were audited"
  for mod in expected do
    unless modules.contains mod do throwError "Required module was not audited: {mod}"
  logInfo m!"Homotopical foundations audit passed: {declarations} declarations in {modules.size} modules."
  logInfo "Standard axioms only; no sorry or citation dependencies."
