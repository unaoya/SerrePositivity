import SerrePositivity.InfinityCategories.Project.Entrypoints.DerivedCoherentBarRetractAll
import Lean
/-!
概要：D 所有の変形 retract の各葉について全宣言の公理依存を検査する。
方針：所属モジュールを固定し、各モジュールの宣言を漏れなく走査する。
規約：許容する公理は propext・Classical.choice・Quot.sound の三つだけ。
使われ方：Retract.All のビルド終端を確認した後に lake env lean で実行する。
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.ClosedSectionDescent,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.ProjectionComponents,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.ProjectorComponents,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.CorrectedInclusion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PrefixDegeneracyNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedOperators,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedComposition,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.TailDegeneracyNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.TailAfterComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PrefixDegeneracyComposition,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PrefixVanishing,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedCoproduct,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PrefixHomotopyAction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedCoproductComposition,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BlockTransport,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.TailAtDegeneracy,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PrefixRightComposition,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PrefixBlockInterchange,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.ShiftUnitIdentity,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.UniversalLabelCoefficients,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.UniversalLabelNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedCoefficientAction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedUniversalCoefficients,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PrefixTermInterchange,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PrefixSums,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PrefixAtZero,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.CompositionExpansion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundaryFaceTerms,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundaryExpansion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundaryFacesOnly,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.FaceHomotopyAction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.LastBoundaryParts,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.LastBoundaryFacesOnly,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.VertexBoundary,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedColumns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedColumnComposition,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedColumnAction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.ShiftUnitCancellation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedUniversalColumn,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.ProjectorCoefficientCriterion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.StageCoefficientCriterion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedIdentityColumn,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.StageCoefficientBase,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedEndColumnAction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.FaceLeftBasedAction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.FaceRightBasedAction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.LabelBoundaryPositive,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.LabelBoundaryLast,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.UniversalCompositeBasis,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.UniversalBoundaryCoefficients,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedFullEndColumnAction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundarySigns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.UniversalBoundarySupport,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundaryCoefficientPositive,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundaryCoefficientComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedCoefficientRestriction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.LabelBoundaryNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.PostcompositionLinear,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedEndBlock,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedEndActionPush,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundaryPostcomposeBasis,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundaryPostcomposeCoefficients,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.StageCoefficientComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DeformationRetract]
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
  logInfo m!"D retract audit passed: {counts.foldl (· + ·) (0 : Nat)} declarations in {modules.size} modules."

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedModuleRetractHomotopyOfDegenerateVanish

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarStageCoefficientComparison
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizationKillsDegenerate
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedModuleInclusionUnconditional
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedModuleInclusionUnconditional_projection
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedModuleProjectionUnconditional_inclusion
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedModuleRetractHomotopyUnconditional
