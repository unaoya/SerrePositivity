import SerrePositivity.BhattScholze.Almost.CompletedModuleTensor
import SerrePositivity.BhattScholze.Almost.AlmostConnectivity
import SerrePositivity.BhattScholze.Almost.AlmostGenerators
import SerrePositivity.BhattScholze.Almost.AlmostTensor
import SerrePositivity.BhattScholze.Almost.AlmostTensorForward

open Lean in
run_cmd do
  let mods : Array Name := #[`SerrePositivity.BhattScholze.Almost.CompletedModuleTensor, `SerrePositivity.BhattScholze.Almost.AlmostConnectivity, `SerrePositivity.BhattScholze.Almost.AlmostGenerators, `SerrePositivity.BhattScholze.Almost.AlmostTensor, `SerrePositivity.BhattScholze.Almost.AlmostTensorForward]
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
