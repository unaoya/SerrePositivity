import SerrePositivity.CLMST.KLOriginalTorFromExcision
import Mathlib.Util.AssertNoSorry

-- These are transparent propositions, not proofs of the missing excision input.
assert_no_sorry SerrePositivity.CLMST.KLCanonicalExcisionSquare
assert_no_sorry SerrePositivity.CLMST.KLFiniteComparisonExcision
#check SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_aic_finiteComparison_excision
#check SerrePositivity.CLMST.exists_andre_extension_finiteComparison_excision_suffices
#check SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_finiteComparison_excision
#print axioms SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_aic_finiteComparison_excision
#print axioms SerrePositivity.CLMST.exists_andre_extension_finiteComparison_excision_suffices
#print axioms SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_finiteComparison_excision

meta section
open Lean Elab Command
private partial def checkKLExcisionPipelineDependencies
    (allowed : NameSet) (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then
      return ← checkKLExcisionPipelineDependencies allowed rest seen
    let seen := seen.insert n
    if allowed.contains n then
      return ← checkKLExcisionPipelineDependencies allowed rest seen
    let some info := (← getEnv).find? n |
      return ← checkKLExcisionPipelineDependencies allowed rest seen
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
    checkKLExcisionPipelineDependencies allowed (deps.toList ++ rest) seen

elab "assert_KL_excision_pipeline_dependencies" : command => do
  let integral := ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral
  let andre := ``SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
  let onlyIntegral : NameSet := ({} : NameSet).insert integral
  let seenAIC ← liftCoreM <| checkKLExcisionPipelineDependencies onlyIntegral
    [``SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_aic_finiteComparison_excision] {}
  unless seenAIC.contains integral do
    throwError "Expected existing B-I dependency is missing"
  let seenOriginal ← liftCoreM <| checkKLExcisionPipelineDependencies (onlyIntegral.insert andre)
    [``SerrePositivity.CLMST.exists_andre_extension_finiteComparison_excision_suffices,
     ``SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_finiteComparison_excision] {}
  unless seenOriginal.contains integral && seenOriginal.contains andre do
    throwError "Expected existing B-I and BS 7.14 dependencies are missing"
  logInfo "Conditional KL pipeline: only existing B-I and BS 7.14; excision remains a hypothesis."
end

assert_KL_excision_pipeline_dependencies
