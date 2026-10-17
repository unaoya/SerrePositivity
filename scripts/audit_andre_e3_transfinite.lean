import SerrePositivity.BhattScholze.Andre.Transfinite.Basic
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.isAbsolutelyIntegrallyClosed_directLimit_of_eventual_roots
assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.directLimit_mod_p_pow_surjective
assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.directLimit_mod_p_pow_surjective_of_perfectoid
assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.exists_stage_countable_family

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.BhattScholze.Andre.Transfinite.RootClosure,
    `SerrePositivity.BhattScholze.Andre.Transfinite.ResidueFrobenius,
    `SerrePositivity.BhattScholze.Andre.Transfinite.CountableDescent]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do
    throwError "Missing André E3 modules"
  logInfo m!"André E3: {count} declarations audited; standard axioms only."

#print SerrePositivity.BhattScholze.Andre.Transfinite.isAbsolutelyIntegrallyClosed_directLimit_of_eventual_roots
#print SerrePositivity.BhattScholze.Andre.Transfinite.directLimit_mod_p_pow_surjective
#print SerrePositivity.BhattScholze.Andre.Transfinite.directLimit_mod_p_pow_surjective_of_perfectoid
#print SerrePositivity.BhattScholze.Andre.Transfinite.exists_stage_countable_family
