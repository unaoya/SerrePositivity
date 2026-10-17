import SerrePositivity.CLMST.Prop247RankComponentExcision
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.CLMST.prop247_fixed_cone_of_two_canonical_excision
assert_no_sorry SerrePositivity.CLMST.aic_finiteEtaleAway_exists_derivedComplete_common_cover
#print axioms SerrePositivity.CLMST.prop247_aic_rankComponent_annihilators_of_excision
#print axioms SerrePositivity.CLMST.prop247_aic_isogeny_of_rank_component_excision

-- The chosen common-model targets retain only the existing B-I input.
meta section
open Lean Elab Command
private partial def checkProp247RankComponentExcisionDependencies (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← checkProp247RankComponentExcisionDependencies rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkProp247RankComponentExcisionDependencies rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx &&
        n != ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral then
      throwError "Unexpected sorry dependency in Prop 2.4.7 rank component assembly: {n}"
    checkProp247RankComponentExcisionDependencies (deps.toList ++ rest) seen

elab "assert_prop247_rank_component_dependencies" : command => do
  let roots := [``SerrePositivity.CLMST.prop247_aic_rankComponent_annihilators_of_excision,
    ``SerrePositivity.CLMST.prop247_aic_isogeny_of_rank_component_excision]
  let seen ← liftCoreM <| checkProp247RankComponentExcisionDependencies roots {}
  unless seen.contains ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral do
    throwError "Expected existing B-I dependency is missing"
  logInfo "Actual rank component assembly: only existing B-I citation is permitted."
end
assert_prop247_rank_component_dependencies
