import SerrePositivity.CLMST.Prop247CanonicalRankDescent
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.CLMST.prop247_productUnit_isPerfectoidization_of_specified
assert_no_sorry SerrePositivity.CLMST.prop247_rankPerfectoidComparison_ker_of_canonical_excision

assert_no_sorry SerrePositivity.CLMST.prop247_exists_andre_descent_base

assert_no_sorry SerrePositivity.CLMST.prop247_fixed_cone_of_two_canonical_excision
assert_no_sorry SerrePositivity.CLMST.aic_finiteEtaleAway_exists_derivedComplete_common_cover
#print axioms SerrePositivity.CLMST.prop247_exists_canonical_generalRank_descent_data

-- The chosen common-model targets retain only the existing B-I input.
meta section
open Lean Elab Command
private partial def checkProp247CanonicalRankDescentDependencies (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← checkProp247CanonicalRankDescentDependencies rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkProp247CanonicalRankDescentDependencies rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx &&
        n != ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral then
      throwError "Unexpected sorry dependency in Prop 2.4.7 canonical general rank descent data: {n}"
    checkProp247CanonicalRankDescentDependencies (deps.toList ++ rest) seen

elab "assert_prop247_canonical_rank_dependencies" : command => do
  let roots := [``SerrePositivity.CLMST.prop247_exists_canonical_generalRank_descent_data]
  let seen ← liftCoreM <| checkProp247CanonicalRankDescentDependencies roots {}
  unless seen.contains ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral do
    throwError "Expected existing B-I dependency is missing"
  logInfo "Actual general rank descent data: only existing B-I citation is permitted."
end
assert_prop247_canonical_rank_dependencies
