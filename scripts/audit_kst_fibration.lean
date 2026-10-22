import SerrePositivity.KST.Fibration
import Lean.Util.CollectAxioms

/-! K-F の私有宣言を含む全宣言と推移的公理依存を検査する。 -/

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[`SerrePositivity.KST.Fibration.WeakEquivalences,
    `SerrePositivity.KST.Fibration.Extension]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.KST.Fibration).isPrefixOf mod do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "K-F: ModelCategory assumption in type of {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "K-F: unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if count == 0 then throwError "K-F: no declarations audited"
  for mod in expected do
    unless modules.contains mod do throwError "K-F: required module missing: {mod}"
  logInfo m!"K-F: {count} declarations in {modules.size} modules audited; standard axioms only."
