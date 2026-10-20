import SerrePositivity.KST.LocalizingInvariants
import Lean.Util.CollectAxioms

/-! K-5 抽象部分の私有宣言と推移的公理依存・宣言型を監査する。 -/

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.KST.LocalizingInvariants.StableCategories,
    `SerrePositivity.KST.LocalizingInvariants.ExactEnrichment,
    `SerrePositivity.KST.LocalizingInvariants.StableInfinity,
    `SerrePositivity.KST.LocalizingInvariants.VerdierSequence,
    `SerrePositivity.KST.LocalizingInvariants.VerdierDiagrams,
    `SerrePositivity.KST.LocalizingInvariants.Invariant,
    `SerrePositivity.KST.LocalizingInvariants.ValueHomotopy,
    `SerrePositivity.KST.LocalizingInvariants.SplitFiberGroups]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.KST.LocalizingInvariants).isPrefixOf mod do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "K-5: ModelCategory assumption in type of {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "K-5: unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if count == 0 then throwError "K-5: no declarations audited"
  for mod in expected do
    unless modules.contains mod do throwError "K-5: required module missing: {mod}"
  logInfo m!"K-5: {count} declarations in {modules.size} modules audited; standard axioms only."
