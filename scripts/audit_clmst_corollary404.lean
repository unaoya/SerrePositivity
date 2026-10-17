import SerrePositivity.CLMST.Corollary404
import SerrePositivity.CLMST.Inputs.CohomologyVanishing
import Mathlib.Util.PrintSorries

#check SerrePositivity.CLMST.klFiniteComparisonExcision_of_perfectoid
#check SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput
#check SerrePositivity.CLMST.corollary_4_0_4
#print axioms SerrePositivity.CLMST.corollary_4_0_4

#print sorries SerrePositivity.CLMST.corollary_4_0_4
#print axioms SerrePositivity.CLMST.Inputs.corollary_4_0_4
#print sorries SerrePositivity.CLMST.Inputs.corollary_4_0_4

meta section
open Lean Elab Command
private partial def checkKLCohomologyExcisionDependencies
    (allowed : NameSet) (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then
      return ← checkKLCohomologyExcisionDependencies allowed rest seen
    let seen := seen.insert n
    if allowed.contains n then
      return ← checkKLCohomologyExcisionDependencies allowed rest seen
    let some info := (← getEnv).find? n |
      return ← checkKLCohomologyExcisionDependencies allowed rest seen
    match info with
    | .axiomInfo _ =>
      unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
        throwError "Unexpected axiom in the KL Cor 4.0.4 proof: {n}"
    | _ => pure ()
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx then
      throwError "Unapproved citation in the KL Cor 4.0.4 proof: {n}"
    checkKLCohomologyExcisionDependencies allowed (deps.toList ++ rest) seen

elab "assert_KL_cohomology_excision_dependencies" : command => do
  let env ← getEnv
  let original := env.find? ``SerrePositivity.CLMST.Inputs.corollary_4_0_4
  let proved := env.find? ``SerrePositivity.CLMST.corollary_4_0_4
  match original, proved with
  | some a, some b =>
    unless a.levelParams == b.levelParams && a.type == b.type do
      throwError "Cor 4.0.4 signatures differ"
  | _, _ => throwError "Missing Cor 4.0.4 declaration"
  let integral := ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral
  let arc := ``SerrePositivity.BhattScholze.Inputs.perfectoidization_excision_isPullback
  let allowed : NameSet := (({} : NameSet).insert integral).insert arc
  let seen ← liftCoreM <| checkKLCohomologyExcisionDependencies allowed
    [``SerrePositivity.CLMST.corollary_4_0_4,
     ``SerrePositivity.CLMST.Inputs.corollary_4_0_4,
     ``SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput] {}
  unless seen.contains integral && seen.contains arc do
    throwError "Expected B-I and BS Cor 8.12 dependencies are missing"
  logInfo "KL Cor 4.0.4: only B-I and BS Cor 8.12; no Cor 4.0.4 citation."
end

assert_KL_cohomology_excision_dependencies
