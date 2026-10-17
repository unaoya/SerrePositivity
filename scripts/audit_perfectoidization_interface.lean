import SerrePositivity.BhattScholze.PerfectoidizationInterface
import Lean.Util.CollectAxioms

-- 界面の全宣言の推移的依存を検査する。存在入力は追加しない。
open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modulePrefix := `SerrePositivity.BhattScholze.PerfectoidizationInterface
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless modulePrefix.isPrefixOf env.header.modules[idx.toNat]!.module do continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax =>
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains ax)
    unless unexpected.isEmpty do
      throwError "非標準公理への依存: {name}: {unexpected}"
    count := count + 1
  if count == 0 then throwError "界面の監査対象宣言がありません"
  logInfo m!"PerfectoidizationInterface 公理監査成功: {count} 宣言、標準 3 公理のみ。"
