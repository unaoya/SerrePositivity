-- lake build SerrePositivity.Spectra.Foundations の後に実行する。
-- スペクトルと、そのための共通圏論・群論の公開宣言を標準公理のみで監査する。
import SerrePositivity.Spectra.Foundations
import SerrePositivity.CategoryTheory.Enriched.RepresentedMapping

import SerrePositivity.Spectra.Pointed.SmashPushoutProduct
import SerrePositivity.Spectra.ModelCategory.PointedGenerators
import SerrePositivity.Spectra.ModelCategory.SimplicialMonoidal
import SerrePositivity.Spectra.ModelCategory.SimplicialLevel
import SerrePositivity.Spectra.ModelCategory.SimplicialWeakEquivalences
import SerrePositivity.Spectra.ModelCategory.SimplicialLevelTensor
import SerrePositivity.Spectra.ModelCategory.SimplicialLevelEnriched
import SerrePositivity.Spectra.ModelCategory.SimplicialHomComparison
import SerrePositivity.Spectra.General.Foundations
import SerrePositivity.Spectra.General.SimplicialComparison
import SerrePositivity.Spectra.ModelCategory.LevelClasses
import SerrePositivity.Spectra.ModelCategory.LevelRecognition
import SerrePositivity.Spectra.ModelCategory.MonoidalLevel
import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators
import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Generators
import Lean.Util.CollectAxioms

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    if name.isInternalDetail then continue
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless #[`SerrePositivity.Spectra, `SerrePositivity.CategoryTheory.FunctorTransport,
        `SerrePositivity.HomotopicalAlgebra.Topological,
        `SerrePositivity.HomotopicalAlgebra.Simplicial.Generators,
        `SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Generators,
        `SerrePositivity.CategoryTheory.Adjunction.Comparison,
        `SerrePositivity.CategoryTheory.Adjunction.Comparison,
        `SerrePositivity.CategoryTheory.Monoidal, `SerrePositivity.CategoryTheory.Adjunction.Comparison, `SerrePositivity.CategoryTheory.Enriched.RepresentedMapping, `SerrePositivity.CategoryTheory.Enriched.Simplicial, `SerrePositivity.CategoryTheory.Enriched.Transport,
        `SerrePositivity.CategoryTheory.Limits,
        `SerrePositivity.GroupTheory.Coxeter, `SerrePositivity.CategoryTheory.Limits,
        `SerrePositivity.CategoryTheory.Limits,
        `SerrePositivity.CategoryTheory.Limits,
        `SerrePositivity.CategoryTheory.Limits,
        `SerrePositivity.CategoryTheory.Limits,
        `SerrePositivity.CategoryTheory.Limits,
        `SerrePositivity.CategoryTheory.Limits].any (·.isPrefixOf mod) do continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax ↦
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains ax)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"
    declarations := declarations + 1
    unless modules.contains mod do modules := modules.push mod
  for expected in #[`SerrePositivity.Spectra.ModelCategory.SimplicialLevel,
      `SerrePositivity.Spectra.ModelCategory.FreePushoutProduct,
      `SerrePositivity.Spectra.ModelCategory.FreePushoutProductModel,
      `SerrePositivity.Spectra.ModelCategory.SimplicialLevelTensor,
      `SerrePositivity.Spectra.ModelCategory.SimplicialLevelEnriched,
      `SerrePositivity.Spectra.ModelCategory.SimplicialHomComparison,
      `SerrePositivity.Spectra.General.EnrichedModel,
      `SerrePositivity.Spectra.ModelCategory.SimplicialWeakEquivalences,
      `SerrePositivity.HomotopicalAlgebra.Topological.WeakEquivalence,
      `SerrePositivity.Spectra.ModelCategory.SimplicialMonoidal,
      `SerrePositivity.Spectra.ModelCategory.PointedGenerators,
      `SerrePositivity.HomotopicalAlgebra.Simplicial.Generators,
      `SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Generators,
      `SerrePositivity.Spectra.ModelCategory.SimplicialCofibrancy,
      `SerrePositivity.Spectra.Pointed.SmashPushoutProduct,
      `SerrePositivity.CategoryTheory.Adjunction.Comparison,
      `SerrePositivity.Spectra.General.ParametrizedCotensor,
      `SerrePositivity.Spectra.General.ParametrizedMapping,
      `SerrePositivity.CategoryTheory.Enriched.RepresentedMapping,
      `SerrePositivity.CategoryTheory.Enriched.RepresentedMapping,
      `SerrePositivity.CategoryTheory.Enriched.RepresentedMapping,
      `SerrePositivity.Spectra.General.MappingFunctorComparison,
      `SerrePositivity.Spectra.General.TensorCotensorEnriched,
      `SerrePositivity.Spectra.General.TensorMappingObject,
      `SerrePositivity.Spectra.General.CotensorMappingObject,
      `SerrePositivity.Spectra.General.TensorMappingSource,
      `SerrePositivity.Spectra.General.CotensorMappingSource,
      `SerrePositivity.Spectra.General.EnrichedMappingObjects,
      `SerrePositivity.Spectra.General.TensorMappingParameter,
      `SerrePositivity.Spectra.General.CotensorMappingParameter,
      `SerrePositivity.Spectra.General.EnrichedMappingParameter,
      `SerrePositivity.Spectra.General.TensorMappingPoints,
      `SerrePositivity.Spectra.General.CotensorMappingPoints,
      `SerrePositivity.Spectra.General.EnrichedRepresentability,
      `SerrePositivity.Spectra.ModelCategory.LevelClasses,
      `SerrePositivity.Spectra.ModelCategory.LevelRecognition,
      `SerrePositivity.Spectra.ModelCategory.LevelAcyclicity,
      `SerrePositivity.Spectra.ModelCategory.LevelSmallness,
      `SerrePositivity.Spectra.ModelCategory.LevelFromGenerators,
      `SerrePositivity.Spectra.ModelCategory.FreeLevelCofibrations,
      `SerrePositivity.Spectra.ModelCategory.MonoidalLevel,
      `SerrePositivity.CategoryTheory.Limits,
      `SerrePositivity.CategoryTheory.Limits,
      `SerrePositivity.Spectra.General.Basic,
      `SerrePositivity.Spectra.General.StructureMaps,
      `SerrePositivity.Spectra.General.FreeLevels,
      `SerrePositivity.Spectra.General.FreeLevelInduction,
      `SerrePositivity.Spectra.General.FreeLevelQuotient,
      `SerrePositivity.Spectra.General.FreeLevelNaturality,
      `SerrePositivity.Spectra.General.Free, `SerrePositivity.Spectra.General.Evaluation,
      `SerrePositivity.Spectra.General.Limits,
      `SerrePositivity.Spectra.General.TensorClosed,
      `SerrePositivity.Spectra.General.PointwiseTensor,
      `SerrePositivity.Spectra.General.Cotensor,
      `SerrePositivity.Spectra.General.MappingObject] do
    unless modules.contains expected do throwError "Required general spectrum module missing: {expected}"
  if declarations == 0 then throwError "No spectra declarations were audited"
  logInfo m!"Spectra and shared foundations audit passed: {declarations} declarations in {modules.size} modules."
  logInfo "Standard axioms only; no sorry dependencies."
