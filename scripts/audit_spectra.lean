-- lake build SerrePositivity.Spectra.Foundations の後に実行する。
-- スペクトルと、そのための共通圏論・群論の公開宣言を標準公理のみで監査する。
import SerrePositivity.Spectra.Foundations
import Lean.Util.CollectAxioms

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    if name.isInternalDetail then continue
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless #[`SerrePositivity.Spectra, `SerrePositivity.CategoryTheory.Monoidal,
        `SerrePositivity.CategoryTheory.Limits,
        `SerrePositivity.GroupTheory.Coxeter, `SerrePositivity.CategoryTheory.FiniteBijection,
        `SerrePositivity.CategoryTheory.FiniteBijectionAction,
        `SerrePositivity.CategoryTheory.FiniteBijectionSum,
        `SerrePositivity.CategoryTheory.FiniteBlockEquiv].any (·.isPrefixOf mod) do continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax ↦
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains ax)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"
    declarations := declarations + 1
    unless modules.contains mod do modules := modules.push mod
  if declarations == 0 then throwError "No spectra declarations were audited"
  logInfo m!"Spectra and shared foundations audit passed: {declarations} declarations in {modules.size} modules."
  logInfo "Standard axioms only; no sorry dependencies."
