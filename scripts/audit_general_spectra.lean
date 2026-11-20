import SerrePositivity.Spectra.General.Foundations
import SerrePositivity.Spectra.General.SimplicialComparison
import Lean.Util.CollectAxioms

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.Spectra.General).isPrefixOf mod do continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax ↦
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains ax)
    unless unexpected.isEmpty do throwError "Unexpected axioms in {name}: {unexpected}"
    declarations := declarations + 1
    unless modules.contains mod do modules := modules.push mod
  for expected in #[`SerrePositivity.Spectra.General.Basic,
      `SerrePositivity.Spectra.General.StructureMaps,
      `SerrePositivity.Spectra.General.FreeLevels,
      `SerrePositivity.Spectra.General.FreeLevelInduction,
      `SerrePositivity.Spectra.General.FreeLevelQuotient,
      `SerrePositivity.Spectra.General.FreeLevelNaturality,
      `SerrePositivity.Spectra.General.Free, `SerrePositivity.Spectra.General.Evaluation,
      `SerrePositivity.Spectra.General.Limits,
      `SerrePositivity.Spectra.General.TensorClosed,
      `SerrePositivity.Spectra.General.PointwiseTensor,
      `SerrePositivity.Spectra.General.PointwiseTensorCoherence,
      `SerrePositivity.Spectra.General.Cotensor,
      `SerrePositivity.Spectra.General.MappingObject,
      `SerrePositivity.Spectra.General.MappingEnrichment,
      `SerrePositivity.Spectra.General.ParametrizedCotensor,
      `SerrePositivity.Spectra.General.ParametrizedMapping,
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
      `SerrePositivity.Spectra.General.EnrichedRepresentability] do
    unless modules.contains expected do throwError "Required module missing: {expected}"
  logInfo m!"General spectra audit passed: {declarations} declarations in {modules.size} modules."
  logInfo "Including internal auxiliaries; standard axioms only; no sorry or citation dependencies."
