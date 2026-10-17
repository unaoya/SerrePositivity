import SerrePositivity.BhattScholze.Andre.MonicRootedExtension
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.Andre.adjoinRoot_faithfullyFlat
assert_no_sorry SerrePositivity.BhattScholze.Andre.exists_monicRootedFaithfullyFlat
assert_no_sorry SerrePositivity.BhattScholze.Andre.expandedPower_quotient_free_faithfullyFlat
assert_no_sorry SerrePositivity.BhattScholze.Andre.monicRelation
assert_no_sorry SerrePositivity.BhattScholze.Andre.monicRelation_isSMulRegular

-- 本レーンの各宣言（生成された宣言も含む）の推移的な公理依存を検査する。
open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[`SerrePositivity.BhattScholze.Andre.OrdinaryMonicRoot,
    `SerrePositivity.BhattScholze.Andre.MonicRelation]
  let mut seen : Array Name := #[]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  unless seen.size == expected.size do
    throwError "Missing André monic root modules"
  logInfo m!"André monic root audit passed: {count} declarations, standard axioms only."
