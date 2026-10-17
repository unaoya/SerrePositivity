import SerrePositivity.BhattScholze.Andre.Transfinite.Basic
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.isAbsolutelyIntegrallyClosed_directLimit_of_eventual_roots
assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.directLimit_mod_p_pow_surjective
assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.directLimit_mod_p_pow_surjective_of_perfectoid
assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.exists_stage_countable_family
assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.isAdicComplete_directLimit_of_countable_upperBound

assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.injective_of_perfectoid_completelyFaithfullyFlat
assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.isAdicComplete_directLimit_of_perfectoid_completelyFaithfullyFlat

assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.omegaOneIndex_nonempty
assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.omegaOneIndex_noMaxOrder
assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.omegaOneIndex_countable_upperBound
assert_no_sorry SerrePositivity.BhattScholze.Andre.Transfinite.omegaOne_directLimit_complete_and_absolutelyIntegrallyClosed

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.BhattScholze.Andre.Transfinite.RootClosure,
    `SerrePositivity.BhattScholze.Andre.Transfinite.ResidueFrobenius,
    `SerrePositivity.BhattScholze.Andre.Transfinite.CountableDescent,
    `SerrePositivity.BhattScholze.Andre.Transfinite.CountableCompletion,
    `SerrePositivity.BhattScholze.Andre.Transfinite.PerfectoidLimitCompleteness,
    `SerrePositivity.BhattScholze.Andre.Transfinite.OmegaOne]
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

#print SerrePositivity.BhattScholze.Andre.Transfinite.isAdicComplete_directLimit_of_countable_upperBound

#print SerrePositivity.BhattScholze.Andre.Transfinite.injective_of_perfectoid_completelyFaithfullyFlat
#print SerrePositivity.BhattScholze.Andre.Transfinite.isAdicComplete_directLimit_of_perfectoid_completelyFaithfullyFlat

#print SerrePositivity.BhattScholze.Andre.Transfinite.omegaOneIndex_nonempty
#print SerrePositivity.BhattScholze.Andre.Transfinite.omegaOneIndex_noMaxOrder
#print SerrePositivity.BhattScholze.Andre.Transfinite.omegaOneIndex_countable_upperBound
#print SerrePositivity.BhattScholze.Andre.Transfinite.omegaOne_directLimit_complete_and_absolutelyIntegrallyClosed
