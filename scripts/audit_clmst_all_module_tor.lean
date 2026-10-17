import SerrePositivity.CLMST.KLAllModule
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.CLMST.allModule_tor_annihilated_of_powerTorsion_and_extension
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_allModule_tor_annihilated
#print axioms SerrePositivity.CLMST.allModule_tor_annihilated_of_powerTorsion_and_extension
#print axioms SerrePositivity.CLMST.perfectoidIdeal_allModule_tor_annihilated

meta section
open Lean Elab Command
private partial def checkStandardOnly (todo : List Name) (seen : NameSet) : CoreM Unit := do
  match todo with
  | [] => pure ()
  | n :: rest =>
    if seen.contains n then return ← checkStandardOnly rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkStandardOnly rest seen
    if let .axiomInfo _ := info then
      unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
        throwError "標準三公理以外への依存: {n}"
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    checkStandardOnly (deps.toList ++ rest) seen
elab "assert_allModule_standard_only" : command => do
  liftCoreM <| checkStandardOnly
    [``SerrePositivity.CLMST.allModule_tor_annihilated_of_powerTorsion_and_extension,
     ``SerrePositivity.CLMST.perfectoidIdeal_allModule_tor_annihilated] {}
end
assert_allModule_standard_only
