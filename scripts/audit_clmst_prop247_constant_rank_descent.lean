import SerrePositivity.CLMST.Prop247ConstantRankDescent
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.CLMST.prop247_fixed_cone_of_two_canonical_excision
assert_no_sorry SerrePositivity.CLMST.aic_finiteEtaleAway_exists_derivedComplete_common_cover
#print axioms SerrePositivity.CLMST.prop247_constantRank_isogeny_of_andre_excision

-- The chosen common-model targets retain only the existing B-I input.
meta section
open Lean Elab Command
private partial def checkProp247ConstantRankDescentDependencies (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← checkProp247ConstantRankDescentDependencies rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkProp247ConstantRankDescentDependencies rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx &&
        n != ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral then
      throwError "Unexpected sorry dependency in Prop 2.4.7 constant rank descent: {n}"
    checkProp247ConstantRankDescentDependencies (deps.toList ++ rest) seen

elab "assert_prop247_constant_rank_descent_dependencies" : command => do
  let roots := [``SerrePositivity.CLMST.prop247_constantRank_isogeny_of_andre_excision]
  let seen ← liftCoreM <| checkProp247ConstantRankDescentDependencies roots {}
  unless seen.contains ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral do
    throwError "Expected existing B-I dependency is missing"
  logInfo "Actual constant rank descent: only existing B-I citation is permitted."
end
assert_prop247_constant_rank_descent_dependencies
