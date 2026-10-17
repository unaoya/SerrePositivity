import SerrePositivity.CLMST.Prop247CompletedDescent
import SerrePositivity.CLMST.Inputs.PerfectoidIsogeny
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.completedBaseChangeTriangle
assert_no_sorry SerrePositivity.DerivedCompletion.completedBaseChangeTriangle_distinguished
assert_no_sorry SerrePositivity.DerivedCompletion.completedBaseChangeTriangleIso
assert_no_sorry SerrePositivity.CLMST.prop247_completedModuleTriangle
assert_no_sorry SerrePositivity.CLMST.prop247_completedModuleTriangle_distinguished
assert_no_sorry SerrePositivity.CLMST.prop247_completedModuleConeIso
assert_no_sorry SerrePositivity.CLMST.prop247_completedModuleConeIso_inclusion
#print axioms SerrePositivity.DerivedCompletion.completedBaseChangeTriangle
#print axioms SerrePositivity.DerivedCompletion.completedBaseChangeTriangle_distinguished
#print axioms SerrePositivity.DerivedCompletion.completedBaseChangeTriangleIso
#print axioms SerrePositivity.CLMST.prop247_completedModuleTriangle
#print axioms SerrePositivity.CLMST.prop247_completedModuleTriangle_distinguished
#print axioms SerrePositivity.CLMST.prop247_completedModuleConeIso
#print axioms SerrePositivity.CLMST.prop247_completedModuleConeIso_inclusion
#print axioms SerrePositivity.CLMST.prop247_isogeny_of_completed_comparison
#print axioms SerrePositivity.CLMST.prop247_isogeny_of_standard_square

meta section
open Lean Elab Command
private partial def checkProp247CompletedAssembly (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← checkProp247CompletedAssembly rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkProp247CompletedAssembly rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx &&
        n != ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral then
      throwError "Unexpected sorry dependency in conditional Prop 2.4.7 assembly: {n}"
    checkProp247CompletedAssembly (deps.toList ++ rest) seen

elab "assert_prop247_completed_assembly_dependencies" : command => do
  let seen ← liftCoreM <| checkProp247CompletedAssembly
    [``SerrePositivity.CLMST.prop247_isogeny_of_completed_comparison,
      ``SerrePositivity.CLMST.prop247_isogeny_of_standard_square] {}
  unless seen.contains ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral do
    throwError "Expected existing B-I dependency is missing"
  unless seen.contains ``SerrePositivity.CLMST.moduleMapConeIsogeny_descent do
    throwError "Expected existing D1-D6 descent route is missing"
  if seen.contains ``SerrePositivity.CLMST.Inputs.proposition_2_4_7 then
    throwError "Conditional assembly must not cite the theorem being eliminated"
  logInfo "Original Prop 2.4.7 map: existing D1-D6 route; only existing B-I citation."
end
assert_prop247_completed_assembly_dependencies
