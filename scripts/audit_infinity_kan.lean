import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanAnodyneMappingLifts
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointedPointedIntervalAnodyne
import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction
import Lean.Util.CollectAxioms

-- IF-W2c: 移動・分割先を定義元で監査し、私有宣言も標準三公理に限る。
open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanAnodyneMappingLifts,
    `SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction,
    `SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointedPointedIntervalAnodyne,
    `SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction
  ]
  let forbidModel : Array Name := #[`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanAnodyneMappingLifts, `SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.LastHornContraction, `SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointedPointedIntervalAnodyne, `SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanSimplexLastContraction]
  for mod in expected do
    unless env.header.modules.any (fun entry => entry.module == mod) do
      throwError "W2c: audit module not imported: {mod}"
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    if forbidModel.contains mod && info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "W2c: ModelCategory assumption in type of {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "W2c: unexpected axioms in {name}: {axioms}"
    unless seen.contains mod do seen := seen.push mod
    count := count + 1
  for mod in expected do
    unless seen.contains mod do throwError "W2c: module has no audited declarations: {mod}"
  logInfo m!"W2c: {count} declarations in {expected.size} modules audited."
