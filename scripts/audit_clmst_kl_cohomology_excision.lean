import SerrePositivity.CLMST.KLCohomologyFromExcision

#check SerrePositivity.CLMST.rPerfd_cohomology_vanishing_of_finiteComparison_excision
#print axioms SerrePositivity.CLMST.rPerfd_cohomology_vanishing_of_finiteComparison_excision

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
        throwError "Unexpected axiom in the conditional KL pipeline: {n}"
    | _ => pure ()
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx then
      throwError "Unapproved citation in the conditional KL pipeline: {n}"
    checkKLCohomologyExcisionDependencies allowed (deps.toList ++ rest) seen

elab "assert_KL_cohomology_excision_dependencies" : command => do
  let integral := ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral
  let andre := ``SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
  let allowed : NameSet := (({} : NameSet).insert integral).insert andre
  let seen ← liftCoreM <| checkKLCohomologyExcisionDependencies allowed
    [``SerrePositivity.CLMST.rPerfd_cohomology_vanishing_of_finiteComparison_excision] {}
  unless seen.contains integral && seen.contains andre do
    throwError "Expected existing B-I and BS 7.14 dependencies are missing"
  logInfo "Both conditional KL conclusions: only existing B-I and BS 7.14; no Cor 4.0.4 citation."
end

assert_KL_cohomology_excision_dependencies
