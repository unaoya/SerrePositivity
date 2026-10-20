import SerrePositivity.KST.LocalizingInvariants
import Lean.Util.CollectAxioms

/-! K-5 抽象部分の私有宣言と推移的公理依存・宣言型を監査する。 -/

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.KST.LocalizingInvariants.StableCategories,
    `SerrePositivity.KST.LocalizingInvariants.ExactEnrichment,
    `SerrePositivity.KST.LocalizingInvariants.StableInfinity,
    `SerrePositivity.KST.LocalizingInvariants.VerdierSequence,
    `SerrePositivity.KST.LocalizingInvariants.VerdierDiagrams,
    `SerrePositivity.KST.LocalizingInvariants.Invariant,
    `SerrePositivity.KST.LocalizingInvariants.ValueHomotopy,
    `SerrePositivity.KST.LocalizingInvariants.SplitFiberGroups,
    `SerrePositivity.KST.LocalizingInvariants.ZeroCategory,
    `SerrePositivity.KST.LocalizingInvariants.ZeroMaps,
    `SerrePositivity.KST.LocalizingInvariants.ExactMapHomotopy,
    `SerrePositivity.KST.LocalizingInvariants.VerdierPresentation,
    `SerrePositivity.KST.LocalizingInvariants.AbstractFiberSequence,
    `SerrePositivity.KST.LocalizingInvariants.FiberDetection,
    `SerrePositivity.KST.LocalizingInvariants.RawFiberSpectrum,
    `SerrePositivity.KST.LocalizingInvariants.PointedFiberLimit,
    `SerrePositivity.KST.LocalizingInvariants.RawFiberInfinityCone,
    `SerrePositivity.KST.LocalizingInvariants.LimitVertexTransport,
    `SerrePositivity.KST.LocalizingInvariants.BFFiberInfinityCone,
    `SerrePositivity.KST.LocalizingInvariants.BFFiberSquare,
    `SerrePositivity.KST.LocalizingInvariants.StrictConeTransport,
    `SerrePositivity.KST.LocalizingInvariants.ConeEdgeLeg,
    `SerrePositivity.KST.LocalizingInvariants.SpectrumHomClass,
    `SerrePositivity.KST.LocalizingInvariants.SpectrumConeLeg,
    `SerrePositivity.KST.LocalizingInvariants.ReplacedFiberLeg,
    `SerrePositivity.KST.LocalizingInvariants.HomotopyFiberLeg,
    `SerrePositivity.KST.LocalizingInvariants.ConeSquareLeg,
    `SerrePositivity.KST.LocalizingInvariants.HomotopyFiberSquareLeg,
    `SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyClass,
    `SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyFunctor,
    `SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyComparison,
    `SerrePositivity.KST.LocalizingInvariants.CoherentSplitFiberGroups,
    `SerrePositivity.KST.LocalizingInvariants.FiberSquareComparison,
    `SerrePositivity.KST.LocalizingInvariants.FiberSequenceComparison,
    `SerrePositivity.KST.LocalizingInvariants.BFFiberSquareArrows,
    `SerrePositivity.KST.LocalizingInvariants.FiberPiComparison,
    `SerrePositivity.KST.LocalizingInvariants.FiberLongExact,
    `SerrePositivity.KST.LocalizingInvariants.SpectrumEdgePi,
    `SerrePositivity.KST.LocalizingInvariants.NativeFiberSequence,
    `SerrePositivity.KST.LocalizingInvariants.InvariantPiComparison,
    `SerrePositivity.KST.LocalizingInvariants.InvariantLongExact,
    `SerrePositivity.KST.LocalizingInvariants.NativeFiberDetection,
    `SerrePositivity.KST.LocalizingInvariants.InvariantFiberDetection,
    `SerrePositivity.KST.LocalizingInvariants.BinaryMappingExt,
    `SerrePositivity.KST.LocalizingInvariants.CotensorAddition,
    `SerrePositivity.KST.LocalizingInvariants.CotensorHomClasses,
    `SerrePositivity.KST.LocalizingInvariants.CotensorMultiplication,
    `SerrePositivity.KST.LocalizingInvariants.SpectrumBinaryGroups,
    `SerrePositivity.KST.LocalizingInvariants.SpectrumBinaryMaps,
    `SerrePositivity.KST.LocalizingInvariants.SpectrumComponentClass,
    `SerrePositivity.KST.LocalizingInvariants.SpectrumMultiplication,
    `SerrePositivity.KST.LocalizingInvariants.SpectrumMultiplicationGroups,
    `SerrePositivity.KST.LocalizingInvariants.SpectrumZeroClass,
    `SerrePositivity.KST.LocalizingInvariants.SplitProductAxes,
    `SerrePositivity.KST.LocalizingInvariants.SplitProductComparison,
    `SerrePositivity.KST.LocalizingInvariants.SplitProductEquivalence,
    `SerrePositivity.KST.LocalizingInvariants.SplitProductShear,
    `SerrePositivity.KST.LocalizingInvariants.FiberProductDecomposition,
    `SerrePositivity.KST.LocalizingInvariants.InvariantProductDecomposition,
    `SerrePositivity.KST.LocalizingInvariants.AdjointLocalization,
    `SerrePositivity.KST.LocalizingInvariants.AdjointVerdier,
    `SerrePositivity.KST.LocalizingInvariants.LaxStableCategory,
    `SerrePositivity.KST.LocalizingInvariants.SemiorthogonalDecomposition,
    `SerrePositivity.KST.LocalizingInvariants.StableValueFunctor,
    `SerrePositivity.KST.LocalizingInvariants.SemiorthogonalInvariant,
    `SerrePositivity.KST.LocalizingInvariants.ZeroArrowFamily,
    `SerrePositivity.KST.LocalizingInvariants.LaxInclusions,
    `SerrePositivity.KST.LocalizingInvariants.LaxInclusionExact,
    `SerrePositivity.KST.LocalizingInvariants.InitialPrismTwoEndpoints,
    `SerrePositivity.KST.LocalizingInvariants.LaxInitialBoundary,
    `SerrePositivity.KST.LocalizingInvariants.PinchedPrecomposeEquivalence,
    `SerrePositivity.KST.LocalizingInvariants.RelativeInitialAdjunction,
    `SerrePositivity.KST.LocalizingInvariants.LaxDAdjunction,
    `SerrePositivity.KST.LocalizingInvariants.RelativeInitialVertexIso,
    `SerrePositivity.KST.LocalizingInvariants.LaxProjectionKernel]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.KST.LocalizingInvariants).isPrefixOf mod do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "K-5: ModelCategory assumption in type of {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "K-5: unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if count == 0 then throwError "K-5: no declarations audited"
  for mod in expected do
    unless modules.contains mod do throwError "K-5: required module missing: {mod}"
  logInfo m!"K-5: {count} declarations in {modules.size} modules audited; standard axioms only."
