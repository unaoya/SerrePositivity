import SerrePositivity.BhattScholze.PerfectoidizationInterface
import Lean.Util.CollectAxioms

-- 界面の全宣言の推移的依存を検査する。存在入力は追加しない。
open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modulePrefix := `SerrePositivity.BhattScholze.PerfectoidizationInterface
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless modulePrefix.isPrefixOf env.header.modules[idx.toNat]!.module do continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax =>
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains ax)
    unless unexpected.isEmpty do
      throwError "非標準公理への依存: {name}: {unexpected}"
    count := count + 1
    let mod := env.header.modules[idx.toNat]!.module
    unless seen.contains mod do seen := seen.push mod
  if count == 0 then throwError "界面の監査対象宣言がありません"
  let expected := #[
    `SerrePositivity.BhattScholze.PerfectoidizationInterface.Setup,
    `SerrePositivity.BhattScholze.PerfectoidizationInterface.Derived,
    `SerrePositivity.BhattScholze.PerfectoidizationInterface.Completion,
    `SerrePositivity.BhattScholze.PerfectoidizationInterface.LimitData,
    `SerrePositivity.BhattScholze.PerfectoidizationInterface.ExcisionDiagram,
    `SerrePositivity.BhattScholze.PerfectoidizationInterface.Interface,
    `SerrePositivity.BhattScholze.PerfectoidizationInterface.InitialBridge,
    `SerrePositivity.BhattScholze.PerfectoidizationInterface.IntegralExistence]
  for mod in expected do
    unless seen.contains mod do throwError "監査から欠けているモジュール: {mod}"
  unless env.contains
      `SerrePositivity.BhattScholze.PerfectoidizationInterface.PerfectoidizationInterfaceE3 do
    throwError "E3 界面の構造体がありません"
  logInfo m!"PerfectoidizationInterface 公理監査成功: {seen.size} モジュール {count} 宣言、標準 3 公理のみ。"
