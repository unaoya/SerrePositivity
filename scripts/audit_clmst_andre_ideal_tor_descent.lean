import SerrePositivity.CLMST.AndrePerfectoidIdealTorDescent
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_baseChangedPerfectoidization
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_baseChanged_aic_principal_cover
#print axioms SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_baseChangedPerfectoidization
#print axioms SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_baseChanged_aic_principal_cover
#print axioms SerrePositivity.CLMST.exists_andre_extension_descends_perfectoidIdeal_powerTorsionTorInput

meta section
open Lean Elab Command
private partial def checkAndreIdealTorDependencies
    (allowed : Name) (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then
      return ← checkAndreIdealTorDependencies allowed rest seen
    let seen := seen.insert n
    if n == allowed then
      return ← checkAndreIdealTorDependencies allowed rest seen
    let some info := (← getEnv).find? n |
      return ← checkAndreIdealTorDependencies allowed rest seen
    match info with
    | .axiomInfo _ =>
      unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
        throwError "Unexpected axiom in Andre ideal Tor descent: {n}"
    | _ => pure ()
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx then
      throwError "Unapproved citation in Andre ideal Tor descent: {n}"
    checkAndreIdealTorDependencies allowed (deps.toList ++ rest) seen

elab "assert_andre_ideal_Tor_dependencies" : command => do
  let allowed := ``SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
  let seen ← liftCoreM <| checkAndreIdealTorDependencies allowed
    [``SerrePositivity.CLMST.exists_andre_extension_descends_perfectoidIdeal_powerTorsionTorInput] {}
  unless seen.contains allowed do
    throwError "Expected existing BS 7.14 dependency is missing"
  logInfo "One Andre extension for all ideal Tor tests: only existing BS 7.14 plus standard three axioms."
end

assert_andre_ideal_Tor_dependencies
