import SerrePositivity.InfinityCategories.Project.Entrypoints.Cocartesian
import SerrePositivity.InfinityCategories.Project.Entrypoints.F1
import SerrePositivity.InfinityCategories.Project.Entrypoints.F1B

/-!
概要：F1 と F1B の集約を同時に読み込み、公開宣言の名前衝突を検査する。
方針：Lean の import 時の重複宣言検出を使い、両レーンの宣言が実際に読まれたことも確認する。
規約：straightening を含む F1 の集約はこの検査だけで読み、F1B の公理監査とは分ける。
使われ方：F1B の保存前に対象二つの同時ビルドと合わせて実行する。
-/

open Lean in
run_cmd do
  let oldAuditPrefix1 := `SerrePositivity.InfinityCategories.F1
  let klw1AuditLayout1 ← IO.ofExcept <| Lean.Json.parse (← IO.FS.readFile "scripts/refactor/targets/bulk-kl-module-map.json")
  let klw1AuditLayout1 ← IO.ofExcept klw1AuditLayout1.getObj?
  let klw1AuditOwners1 := Std.HashSet.ofList (klw1AuditLayout1.toList.filterMap fun (source, dest) =>
    if oldAuditPrefix1.isPrefixOf source.toName then dest.getStr?.toOption.map String.toName else none)
  let oldAuditPrefix2 := `SerrePositivity.InfinityCategories.F1B
  let klw1AuditLayout2 ← IO.ofExcept <| Lean.Json.parse (← IO.FS.readFile "scripts/refactor/targets/bulk-kl-module-map.json")
  let klw1AuditLayout2 ← IO.ofExcept klw1AuditLayout2.getObj?
  let klw1AuditOwners2 := Std.HashSet.ofList (klw1AuditLayout2.toList.filterMap fun (source, dest) =>
    if oldAuditPrefix2.isPrefixOf source.toName then dest.getStr?.toOption.map String.toName else none)
  let env ← getEnv
  let mut f1Count : Nat := 0
  let mut f1bCount : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    if (oldAuditPrefix1.isPrefixOf mod || klw1AuditOwners1.contains mod) then
      f1Count := f1Count + 1
    if (oldAuditPrefix2.isPrefixOf mod || klw1AuditOwners2.contains mod) then
      f1bCount := f1bCount + 1
  if f1Count == 0 || f1bCount == 0 then
    throwError "F1/F1B collision audit did not load declarations from both lanes"
  logInfo m!"F1/F1B collision audit passed: {f1Count} F1 and {f1bCount} F1B declarations."

#check @SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldBaseChange_overPullbackMap
#check @SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.F1B.cocartesianScaffoldBaseChange_overPullbackMap
