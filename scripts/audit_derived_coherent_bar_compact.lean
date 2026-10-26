import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.All
import Lean
/-!
概要：D 所有の compact 生成元比較 の各葉について全宣言の公理依存を検査する。
方針：所属モジュールを固定し、各モジュールの宣言を漏れなく走査する。
規約：許容する公理は propext・Classical.choice・Quot.sound の三つだけ。
使われ方：Compact.All のビルド終端を確認した後に lake env lean で実行する。
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.RepresentableEvaluation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeHomCriterion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.YonedaHomNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.YonedaNerveIso,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ProjectiveHomCriterion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.GeneratorClosure,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ConeInput,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationModuleNerveIso,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeEvaluationSpace,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationGeneratorClosure,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeAugmentationIdentity,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.HomologyCoconeCriterion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeHomologyColimit,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.FilteredSpaceBridgeInput,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PiTransportMap,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.BridgePreservation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModulePiTransport,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModulePiHomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.HomologyCharts,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.HomologyChartsPiData,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModuleHomologyCharts,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PinchedModuleMap,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.MooreUliftNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.StandardMooreNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PinchedMooreNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.TruncationHomologyNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PinchedHomologyNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PinchedPiCohomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationValueCohomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PinchedModuleCohomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PinchedCohomologyNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.CoherentCosliceEvaluationComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.CosliceUnderlyingValueComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.CosliceUnderlyingValueNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.LinearUnderlyingValueComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EdgewisePiComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EdgewisePiNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UliftPointedSimplex,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UliftPointedFilling,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UliftPiComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UliftPiNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UliftPiZeroComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.StandardPiCohomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModuleZeroChartExtension,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.LinearLiftPiCharts,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.OppositePiZeroComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.LinearHomCohomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PiChartTransport,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PiChartEquivalence,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.StandardClosedPostcomposition,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UnderlyingValueRestriction,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UliftPiTransport,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UliftPiChart,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeHomPiChart,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeHomSmallPiChart,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PiChartSpaceCast,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeHomClosedNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModuleValuePiChart,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModuleValueNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModuleValueEdgeEquality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationPiChart,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationScalarClosedMap,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationVertexPiChart,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationClosedNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationEdgeNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.CoconeLegNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationCoconeGeometry,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationHomologyCoefficients,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationHomologyCharts,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationChartNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationChartLegs,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeEvaluationPiData,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeEvaluationPreservation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UnconditionalConeInput,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UnconditionalPerfectInput]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut counts : Array Nat := modules.map (fun _ => 0)
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.header.modules[index.toNat]!.module
    let some position := modules.idxOf? moduleName | continue
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "Forbidden axiom {dependency} in {name}"
    counts := counts.modify position (· + 1)
  for position in [:modules.size] do
    unless counts[position]! > 0 do
      throwError "No declarations checked in {modules[position]!}"
  logInfo m!"D compact audit passed: {counts.foldl (· + ·) (0 : Nat)} declarations in {modules.size} modules."

#check SerrePositivity.InfinityCategories.dgKappaConeInput_unconditional
#check SerrePositivity.InfinityCategories.dgKappaPerfectInput_unconditional
#check SerrePositivity.InfinityCategories.dgKappaConeInput_unconditional_derivedFullyFaithful
#print axioms SerrePositivity.InfinityCategories.dgKappaConeInput_unconditional
