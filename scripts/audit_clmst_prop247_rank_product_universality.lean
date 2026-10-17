import SerrePositivity.CLMST.Prop247RankProductUniversality
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.CLMST.prop247_productUnit_isPerfectoidization_of_specified

#print axioms SerrePositivity.CLMST.prop247_rankProductUnit_isPerfectoidization_of_finite_coefficients

-- The chosen common-model targets retain only the existing B-I input.
meta section
open Lean Elab Command
private partial def checkProp247RankProductUniversalityDependencies (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← checkProp247RankProductUniversalityDependencies rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkProp247RankProductUniversalityDependencies rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx &&
        n != ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral then
      throwError "Unexpected sorry dependency in Prop 2.4.7 actual rank product unit: {n}"
    checkProp247RankProductUniversalityDependencies (deps.toList ++ rest) seen

elab "assert_prop247_rank_product_dependencies" : command => do
  let roots := [``SerrePositivity.CLMST.prop247_rankProductUnit_isPerfectoidization_of_finite_coefficients]
  let seen ← liftCoreM <| checkProp247RankProductUniversalityDependencies roots {}
  unless seen.contains ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral do
    throwError "Expected existing B-I dependency is missing"
  logInfo "Actual rank product unit: only existing B-I citation is permitted."
end
assert_prop247_rank_product_dependencies
