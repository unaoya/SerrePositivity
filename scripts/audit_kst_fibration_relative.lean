import SerrePositivity.KST.Fibration.Relative.All
import Lean.Util.CollectAxioms

/-!
概要：K-B2 の全所有宣言を私有名も含めて公理監査する。
方針：環境の宣言を定義元モジュールで選び、推移的公理を列挙する。
規約：標準三公理のみ許可し、宣言型の ModelCategory 仮定を拒否する。
使われ方：Relative.All の対象ビルド後の専用監査。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.KST.Fibration.Relative.FiniteCoordinates,
    `SerrePositivity.KST.Fibration.Relative.CoordinatePostcomp,
    `SerrePositivity.KST.Fibration.Relative.AdditivityFiber]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.KST.Fibration.Relative).isPrefixOf mod do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "K-B2: ModelCategory assumption in type of {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "K-B2: unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if count == 0 then throwError "K-B2: no declarations audited"
  for mod in expected do
    unless modules.contains mod do throwError "K-B2: required module missing: {mod}"
  logInfo m!"K-B2: {count} declarations in {modules.size} modules audited; standard axioms only."
