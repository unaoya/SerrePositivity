import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.All
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
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.ClosedSectionDescent,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.ProjectionComponents,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.ProjectorComponents,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.CorrectedInclusion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixDegeneracyNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedOperators,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedComposition,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.TailDegeneracyNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.TailAfterComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixDegeneracyComposition,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixVanishing,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedCoproduct,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixHomotopyAction,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedCoproductComposition,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BlockTransport,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.TailAtDegeneracy,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixRightComposition,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixBlockInterchange,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.ShiftUnitIdentity,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.UniversalLabelCoefficients,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.UniversalLabelNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedCoefficientAction,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedUniversalCoefficients,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixTermInterchange,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixSums,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixAtZero,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.CompositionExpansion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BoundaryFaceTerms,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BoundaryExpansion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BoundaryFacesOnly,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.FaceHomotopyAction,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.LastBoundaryParts,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.LastBoundaryFacesOnly,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.VertexBoundary,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedColumns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedColumnComposition,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedColumnAction,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.ShiftUnitCancellation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedUniversalColumn,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.ProjectorCoefficientCriterion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.StageCoefficientCriterion]
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

#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish
#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizedModuleRetractHomotopyOfDegenerateVanish
