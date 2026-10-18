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
    `SerrePositivity.KST.Spectra.PathSpace,
    `SerrePositivity.KST.Spectra.PointedMappingParameters,
    `SerrePositivity.KST.Spectra.IntervalContraction,
    `SerrePositivity.KST.Spectra.PathReparametrization,
    `SerrePositivity.KST.Spectra.PathContractionBody,
    `SerrePositivity.KST.Spectra.PathContraction,
    `SerrePositivity.KST.Spectra.HomotopyConstant,
    `SerrePositivity.KST.Spectra.PathContractibility,
    `SerrePositivity.KST.Spectra.IntervalBoundary,
    `SerrePositivity.KST.Spectra.EndpointCircle,
    `SerrePositivity.KST.Spectra.PointedCofiber,
    `SerrePositivity.KST.Spectra.CofiberMappingPullback,
    `SerrePositivity.KST.Spectra.LoopPathFiber,
    `SerrePositivity.KST.Spectra.HomotopyIso,
    `SerrePositivity.KST.Spectra.ContractibleTotalSequence,
    `SerrePositivity.KST.Spectra.LoopHomotopyGroups,
    `SerrePositivity.KST.Spectra.OmegaSpectrumTransitions,
    `SerrePositivity.KST.Spectra.PointedIntervalAnodyne,
    `SerrePositivity.KST.Spectra.AnodyneMappingLifts,
    `SerrePositivity.KST.Spectra.BoundaryFaces,
    `SerrePositivity.KST.Spectra.BoundaryFilling,
    `SerrePositivity.KST.Spectra.ZeroConnectingInjectivity,
    `SerrePositivity.KST.Spectra.LoopZeroHomotopy,
    `SerrePositivity.KST.Spectra.OmegaSpectrumZeroGroups,
    `SerrePositivity.KST.Spectra.SpectrumHomotopyGroups,
    `SerrePositivity.KST.Spectra.SpectrumHomotopyFunctor,
    `SerrePositivity.KST.Spectra.SpectrumHomotopyEquivalences,
    `SerrePositivity.KST.Spectra.PointedHomotopy,
    `SerrePositivity.KST.Spectra.MonoRightHomotopyEquivalence,
    `SerrePositivity.KST.Spectra.AnodyneHomotopyEquivalence,
    `SerrePositivity.KST.Spectra.PointedKanReplacement,
    `SerrePositivity.KST.Spectra.PointedFactorization,
    `SerrePositivity.KST.Spectra.KanSequence,
    `SerrePositivity.KST.Spectra.CofibrantKanSequence,
    `SerrePositivity.KST.Spectra.PostMappingLifts,
    `SerrePositivity.KST.Spectra.CofibrantOmegaSequence,
    `SerrePositivity.KST.Spectra.PointedFiber,
    `SerrePositivity.KST.Spectra.FiberKanSequence,
    `SerrePositivity.KST.Spectra.GroupFiveLemma,
    `SerrePositivity.KST.Spectra.HomotopySquares,
    `SerrePositivity.KST.Spectra.FibrationComparisonPositive,
    `SerrePositivity.KST.Spectra.StageComparisonCoherence,
    `SerrePositivity.KST.Spectra.FibrationNaturalityAt,
    `SerrePositivity.KST.Spectra.PathNaturality,
    `SerrePositivity.KST.Spectra.LoopHomotopyNaturality,
    `SerrePositivity.KST.Spectra.OmegaTransitionNaturality,
    `SerrePositivity.KST.Spectra.SpectrumLevelFunctor,
    `SerrePositivity.KST.Spectra.StageComparisonNaturality,
    `SerrePositivity.KST.Spectra.PointedExtension,
    `SerrePositivity.KST.Spectra.PointedSequence,
    `SerrePositivity.KST.Spectra.KanSequenceReplacement,
    `SerrePositivity.KST.Spectra.HomotopyComponents,
    `SerrePositivity.KST.Spectra.FiberComponents,
    `SerrePositivity.KST.Spectra.FiberComponentNaturality,
    `SerrePositivity.KST.Spectra.FibrationComparisonZero,
    `SerrePositivity.KST.Spectra.FibrationComparison,
    `SerrePositivity.KST.Spectra.LoopFiber,
    `SerrePositivity.KST.Spectra.PostMappingFibration,
    `SerrePositivity.KST.Spectra.FiberOmegaSpectrum,
    `SerrePositivity.KST.Spectra.SpectrumFiberStage,
    `SerrePositivity.KST.Spectra.SpectrumBoundary,
    `SerrePositivity.KST.Spectra.GroupExactTransfer,
    `SerrePositivity.KST.Spectra.SpectrumFibrationSequence,
    `SerrePositivity.KST.Spectra.FilteredHomotopyComparison,
    `SerrePositivity.KST.Spectra.FilteredPointing,
    `SerrePositivity.KST.Spectra.FilteredPiIsomorphism,
    `SerrePositivity.KST.Spectra.FilteredOmegaSpectrum,
    `SerrePositivity.KST.Spectra.FilteredSpectrumHomotopy,
    `SerrePositivity.KST.Spectra.FilteredFiniteMapping,
    `SerrePositivity.KST.Spectra.FilteredFiniteMappingColimit,
    `SerrePositivity.KST.Spectra.FilteredLoopColimit,
    `SerrePositivity.KST.Spectra.FilteredKanColimit,
    `SerrePositivity.KST.Spectra.FilteredHomotopyRepresentatives,
    `SerrePositivity.KST.Spectra.FilteredPointedHomotopy,
    `SerrePositivity.KST.Spectra.FilteredHomotopyGroups,
    `SerrePositivity.KST.Spectra.PullbackKanSequence,
    `SerrePositivity.KST.Spectra.MappingPathSpace,
    `SerrePositivity.KST.Spectra.MappingPathSequence,
    `SerrePositivity.KST.Spectra.SpectrumFibrationReplacement,
    `SerrePositivity.KST.Spectra.SpectrumHomotopyFiber,
    `SerrePositivity.KST.Spectra.HomTensorStrength,
    `SerrePositivity.KST.Spectra.MappingKanSequence,
    `SerrePositivity.KST.Spectra.FreeIntervalBoundary,
    `SerrePositivity.KST.Spectra.FreeInterval,
    `SerrePositivity.KST.Spectra.FreePathSpace,
    `SerrePositivity.KST.Spectra.CofibrantSequenceLifting,
    `SerrePositivity.KST.Spectra.StageTransitionCoherence]
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
