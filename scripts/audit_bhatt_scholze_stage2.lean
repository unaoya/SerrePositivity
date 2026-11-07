import SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcPerfectoidBase
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationMilnor
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationCompletion
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationExtension
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationTilt
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationUntilt
import Lean.Util.CollectAxioms

/-!
概要：段階 II で BS の drafts から本体へ移したモジュールを公理監査する。
方針：下の一覧のモジュールで定義された宣言（生成宣言を含む）について、公理の依存を再帰的に調べる。
規約：標準三公理 propext・Classical.choice・Quot.sound だけを許す。新しいモジュールを取り込むたびに、import と一覧の両方に足す。
使われ方：調整役が取り込みのたびに `lake env lean` で実行する（import するモジュールを先に `lake build`）。
-/

open Lean in
run_cmd do
  let mods : Array Name := #[
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcPerfectoidBase,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationMilnor,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationCompletion,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationExtension,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationTilt,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationUntilt]
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless mods.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "BS stage II: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "BS stage II: no declarations audited"
  logInfo m!"BS stage II audit passed: {count} declarations, standard three axioms only."
