import SerrePositivity.KST.Spectra.D3All
import Lean.Util.CollectAxioms

/-!
概要：Sp-2 専用集約の全 Spectra 宣言と推移的公理依存を監査する。
方針：私有宣言も元モジュールから列挙し、型の ModelCategory と非標準公理を拒否する。
規約：既存集約と既存監査は変更しない。未完の nativeLoop 同値を認証したとは扱わない。
使われ方：d3 の保存単位の独立監査。
-/

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  for mod in #[
      `SerrePositivity.KST.Spectra.PointedParametricUncurryAction,
      `SerrePositivity.KST.Spectra.PointedParametricUncurryPre,
      `SerrePositivity.KST.Spectra.PointedUncurryActionTensor,
      `SerrePositivity.KST.Spectra.PointedUncurryComposition] do
    if env.header.modules.any (·.module == mod) then
      throwError "Sp-2 d3: disconnected leaf imported: {mod}"
  let expected := #[
    `SerrePositivity.KST.Spectra.SpectrumFiniteLimits,
    `SerrePositivity.KST.Spectra.AdjointLoopRelativeFullCoherentComparison,
    `SerrePositivity.KST.Spectra.AdjointLoopRelativeDiagramResolution,
    `SerrePositivity.KST.Spectra.D3ComparisonResolution,
    `SerrePositivity.KST.Spectra.D3NativeLoopSource,
    `SerrePositivity.KST.Spectra.D3RawHomVertices,
    `SerrePositivity.KST.Spectra.D3LoopUnitExtension,
    `SerrePositivity.KST.Spectra.D3LoopSourceComparison,
    `SerrePositivity.KST.Spectra.D3LoopSourceCone,
    `SerrePositivity.KST.Spectra.D3LoopConeRelativeLifting,
    `SerrePositivity.KST.Spectra.D3ComparisonHomLifting,
    `SerrePositivity.KST.Spectra.D3CompositeCorner,
    `SerrePositivity.KST.Spectra.D3SpectrumCorner,
    `SerrePositivity.KST.Spectra.D3CommonRefinement,
    `SerrePositivity.KST.Spectra.D3CommonHom,
    `SerrePositivity.KST.Spectra.D3CommonHomComposition,
    `SerrePositivity.KST.Spectra.D3CommonHomLaws,
    `SerrePositivity.KST.Spectra.D3CommonEnrichment,
    `SerrePositivity.KST.Spectra.D3CommonCoherentComparison,
    `SerrePositivity.KST.Spectra.D3CommonProjectionNaturality,
    `SerrePositivity.KST.Spectra.D3ConeForwardTransport,
    `SerrePositivity.KST.Spectra.D3CommonLoopCone,
    `SerrePositivity.KST.Spectra.D3CommonLoopSquare,
    `SerrePositivity.KST.Spectra.D3CommonLoopInterval,
    `SerrePositivity.KST.Spectra.D3CommonLoopDiagramResolution,
    `SerrePositivity.KST.Spectra.D3CommonLoopDiagramSection]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.KST.Spectra).isPrefixOf mod do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "Sp-2 d3: ModelCategory assumption in type of {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Sp-2 d3: unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if count == 0 then throwError "Sp-2 d3: no declarations audited"
  for mod in expected do
    unless modules.contains mod do throwError "Sp-2 d3: required module missing: {mod}"
  logInfo m!"Sp-2 d3: {count} declarations in {modules.size} modules audited; standard three axioms only."
