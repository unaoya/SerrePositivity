import SerrePositivity.InfinityCategories.Derived.CoherentBar.All
import Lean

/-!
概要：D-bar の所有葉の全宣言の公理依存を検査する。
方針：環境の所属モジュールで選別し、標準三公理のみを許容する。
規約：D の既存集約・既存監査を変更しない。
使われ方：自分の All のビルド後に lake env lean で実行する。
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Module,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.HomDegrees,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.HomEquations,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeDegeneracy,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.RawInclusions,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedGraded,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.DegeneracyOperators,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.EndRebase,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.LabelNormalization,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizationStages,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateSplitting]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"D-bar axiom audit passed: {count} declarations in {seen.size} modules."

#check SerrePositivity.InfinityCategories.dgCoherentBarModule
#check SerrePositivity.InfinityCategories.dgCoherentBarHomDegreeEquiv
#check SerrePositivity.InfinityCategories.dgCoherentBarHomDegreeEquiv_d
#check SerrePositivity.InfinityCategories.dgCoherentBarHomColumnsEquiv
#check SerrePositivity.InfinityCategories.dgCoherentBarClosedColumnsEquiv
#check SerrePositivity.InfinityCategories.dgCoherentBar_native_degenerateTriangle
#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizationStageHomotopy
#check SerrePositivity.InfinityCategories.dgCoherentBarLabelNormalizedEquiv
#check SerrePositivity.InfinityCategories.dgCoherentBarEndRebase_d
