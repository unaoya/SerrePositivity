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
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.YonedaNerveIso]
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
