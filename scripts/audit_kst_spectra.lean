import SerrePositivity.KST.Spectra
import Lean.Util.CollectAxioms

/-!
概要：K-L9 の全宣言の公理依存を監査する。
方針：専用モジュールの私有宣言も列挙し、許可集合外の公理を拒否する。
規約：標準三公理のみ。共有ルートは import しない。
使われ方：Kerodon §3.2、HA §1.4 に沿う実構成の保存単位ごとの検証。
-/

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.KST.Spectra.HomotopyGroups,
    `SerrePositivity.KST.Spectra.HomotopyDegreeZero,
    `SerrePositivity.KST.Spectra.HomotopyInvariance,
    `SerrePositivity.KST.Spectra.Commutativity,
    `SerrePositivity.KST.Spectra.HomotopyIndexing,
    `SerrePositivity.KST.Spectra.HomotopyZeroRelations,
    `SerrePositivity.KST.Spectra.FibrationBoundary,
    `SerrePositivity.KST.Spectra.FibrationSequence,
    `SerrePositivity.KST.Spectra.FibrationExactness,
    `SerrePositivity.KST.Spectra.FibrationNaturality,
    `SerrePositivity.KST.Spectra.FibrationMultiplication,
    `SerrePositivity.KST.Spectra.PointedMapping,
    `SerrePositivity.KST.Spectra.FibrationTower,
    `SerrePositivity.KST.Spectra.TruncatedMapping,
    `SerrePositivity.KST.Spectra.SuspensionLoop,
    `SerrePositivity.KST.Spectra.HomotopyIsomorphism,
    `SerrePositivity.KST.Spectra.OmegaSpectrum,
    `SerrePositivity.KST.Spectra.PointedMappingNaturality,
    `SerrePositivity.KST.Spectra.TruncatedMappingUniversal,
    `SerrePositivity.KST.Spectra.SpectrumMorphisms,
    `SerrePositivity.KST.Spectra.SpectrumMappingVertices,
    `SerrePositivity.KST.Spectra.PointedEnrichment,
    `SerrePositivity.KST.Spectra.TensorMapping,
    `SerrePositivity.KST.Spectra.SuspensionComposition,
    `SerrePositivity.KST.Spectra.EnrichedMappingLaws,
    `SerrePositivity.KST.Spectra.SpectrumMappingComposition,
    `SerrePositivity.KST.Spectra.SpectrumMappingLaws,
    `SerrePositivity.KST.Spectra.SpectrumSimplicialCategory,
    `SerrePositivity.KST.Spectra.CoherentNerve,
    `SerrePositivity.KST.Spectra.PointedInterval,
    `SerrePositivity.KST.Spectra.PathSpace]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.KST.Spectra).isPrefixOf mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "K-L9: unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if count == 0 then throwError "K-L9: no declarations audited"
  for mod in expected do
    unless modules.contains mod do throwError "K-L9: required module missing: {mod}"
  logInfo m!"K-L9: {count} declarations in {modules.size} modules audited; standard three axioms only."
