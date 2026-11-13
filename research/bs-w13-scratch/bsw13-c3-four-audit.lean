import SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralClosureCompletion
import SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralApproximation
import SerrePositivity.BhattScholze.Perfectoidization.Derived.PerfectoidFilteredColimit
import SerrePositivity.BhattScholze.Almost.FiniteEtaleComparison

open Lean in
run_cmd do
  let mods : Array Name := #[`SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralClosureCompletion, `SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralApproximation, `SerrePositivity.BhattScholze.Perfectoidization.Derived.PerfectoidFilteredColimit, `SerrePositivity.BhattScholze.Almost.FiniteEtaleComparison]
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
