import SerrePositivity.CLMST.Prop247Conditional
import SerrePositivity.CLMST.Inputs.PerfectoidIsogeny
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.CLMST.prop247_uniform_of_common_comparison
assert_no_sorry SerrePositivity.CLMST.prop247_completionMap_unit
assert_no_sorry SerrePositivity.CLMST.prop247_tensor_completion_unit_surjective
assert_no_sorry SerrePositivity.moduleMapConeScalar_of_finite_cover
#print axioms SerrePositivity.moduleMapConeScalar_of_finite_cover
#print axioms SerrePositivity.CLMST.prop247_isogeny_of_common_comparison
#check SerrePositivity.CLMST.prop247_isogeny_of_common_comparison

meta section
open Lean Elab Command
private partial def checkProp247Assembly (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← checkProp247Assembly rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkProp247Assembly rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx &&
        n != ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral then
      throwError "Unexpected sorry dependency in conditional Prop 2.4.7 assembly: {n}"
    checkProp247Assembly (deps.toList ++ rest) seen

elab "assert_prop247_assembly_dependencies" : command => do
  let seen ← liftCoreM <| checkProp247Assembly
    [``SerrePositivity.CLMST.prop247_isogeny_of_common_comparison] {}
  unless seen.contains ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral do
    throwError "Expected existing B-I dependency is missing"
  unless seen.contains ``SerrePositivity.CLMST.moduleMapConeIsogeny_descent do
    throwError "Expected existing D1-D6 descent route is missing"
  if seen.contains ``SerrePositivity.CLMST.Inputs.proposition_2_4_7 then
    throwError "Conditional assembly must not cite the theorem being eliminated"
  logInfo "Original Prop 2.4.7 map: existing D1-D6 route; only existing B-I citation."
end
assert_prop247_assembly_dependencies
