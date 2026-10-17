import SerrePositivity.CLMST.Prop247Cone
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.isModuleComplete_of_finitePresentation
assert_no_sorry SerrePositivity.CLMST.prop247_source_isModuleComplete
assert_no_sorry SerrePositivity.CLMST.prop247_cone_isComplete_of_perfectoid_target
#print axioms SerrePositivity.DerivedCompletion.isModuleComplete_of_finitePresentation
#print axioms SerrePositivity.CLMST.prop247_source_isModuleComplete
#print axioms SerrePositivity.CLMST.prop247_cone_isComplete_of_perfectoid_target
#print axioms SerrePositivity.CLMST.prop247_target_isModuleComplete
#print axioms SerrePositivity.CLMST.prop247_cone_isComplete

-- Concrete chosen targets already use B-I in their definitions. Check the exact
-- citation boundary instead of pretending that their types are sorry-free.
meta section
open Lean Elab Command
private partial def checkProp247Dependencies (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← checkProp247Dependencies rest seen
    let seen := seen.insert n
    let some info := (← getEnv).find? n | return ← checkProp247Dependencies rest seen
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx &&
        n != ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral then
      throwError "Unexpected sorry dependency in Prop 2.4.7 cone completeness: {n}"
    checkProp247Dependencies (deps.toList ++ rest) seen

elab "assert_prop247_cone_dependencies" : command => do
  let roots := [``SerrePositivity.CLMST.prop247_target_isModuleComplete,
    ``SerrePositivity.CLMST.prop247_cone_isComplete]
  let seen ← liftCoreM <| checkProp247Dependencies roots {}
  unless seen.contains ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral do
    throwError "Expected existing B-I dependency is missing"
  logInfo "Chosen Prop 2.4.7 cone: only existing B-I citation is permitted."
end
assert_prop247_cone_dependencies

noncomputable section
universe u
open SerrePositivity SerrePositivity.CLMST

-- Actual cone of the zero map R → R; no étaleness or regularity of p.
theorem audit_prop247_zero_map_complete
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) :
    DerivedCompletion.IsComplete R (p : R) (moduleMapCone R (0 : R →ₗ[R] R)) :=
  prop247_cone_isComplete_of_perfectoid_target R R p hR R hR 0

assert_no_sorry audit_prop247_zero_map_complete
#print axioms audit_prop247_zero_map_complete
