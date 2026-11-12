import SerrePositivity.InfinityCategories.Project.Entrypoints.DerivedCoherentBarCompactAll
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
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.RepresentableEvaluation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeHomCriterion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.YonedaHomNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.YonedaNerveIso,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ProjectiveHomCriterion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.GeneratorClosure,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ConeInput,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationModuleNerveIso,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeEvaluationSpace,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationGeneratorClosure,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeAugmentationIdentity,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.HomologyCoconeCriterion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeHomologyColimit,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.FilteredSpaceBridgeInput,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PiTransportMap,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.BridgePreservation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModulePiTransport,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModulePiHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.HomologyCharts,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.HomologyChartsPiData,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModuleHomologyCharts,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PinchedModuleMap,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.MooreUliftNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.StandardMooreNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PinchedMooreNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.TruncationHomologyNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PinchedHomologyNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PinchedPiCohomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationValueCohomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PinchedModuleCohomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PinchedCohomologyNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.CoherentCosliceEvaluationComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.CosliceUnderlyingValueComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.CosliceUnderlyingValueNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.LinearUnderlyingValueComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EdgewisePiComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EdgewisePiNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPointedSimplex,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPointedFilling,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPiComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPiNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPiZeroComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.StandardPiCohomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModuleZeroChartExtension,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.LinearLiftPiCharts,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.OppositePiZeroComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.LinearHomCohomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PiChartTransport,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PiChartEquivalence,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.StandardClosedPostcomposition,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UnderlyingValueRestriction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPiTransport,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPiChart,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeHomPiChart,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeHomSmallPiChart,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PiChartSpaceCast,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeHomClosedNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModuleValuePiChart,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModuleValueNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModuleValueEdgeEquality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationPiChart,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationScalarClosedMap,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationVertexPiChart,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationClosedNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationEdgeNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.CoconeLegNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationCoconeGeometry,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationHomologyCoefficients,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationHomologyCharts,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationChartNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationChartLegs,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeEvaluationPiData,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeEvaluationPreservation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UnconditionalConeInput,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UnconditionalPerfectInput]
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

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaPerfectInput_unconditional
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional_derivedFullyFaithful
#print axioms SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional
