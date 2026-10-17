import SerrePositivity.CLMST.CanonicalExcisionTorInput

#check SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_two_canonical_excision
#print axioms SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_two_canonical_excision

-- B-I is used only by the existing identification of the finite product's
-- perfectoidization. Excision remains a hypothesis, not a new cited input.
-- In particular, Cor 4.0.4, Prop 2.4.9(a), Cor 8.12 and BS 7.14 are not allowed
-- as hidden dependencies of this local transport theorem.
meta section
open Lean Elab Command
private partial def checkCanonicalExcisionTorDependencies
    (allowed : Name) (todo : List Name) (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then
      return ← checkCanonicalExcisionTorDependencies allowed rest seen
    let seen := seen.insert n
    if n == allowed then
      return ← checkCanonicalExcisionTorDependencies allowed rest seen
    let some info := (← getEnv).find? n |
      return ← checkCanonicalExcisionTorDependencies allowed rest seen
    match info with
    | .axiomInfo _ =>
      unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
        throwError "Unexpected axiom in canonical-excision Tor transport: {n}"
    | _ => pure ()
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx then
      throwError "Unapproved citation in canonical-excision Tor transport: {n}"
    checkCanonicalExcisionTorDependencies allowed (deps.toList ++ rest) seen

elab "assert_two_canonical_excision_Tor_dependencies" : command => do
  let allowed := ``SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral
  let seen ← liftCoreM <| checkCanonicalExcisionTorDependencies allowed
    [``SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_two_canonical_excision] {}
  unless seen.contains allowed do
    throwError "Expected existing B-I dependency is missing"
  logInfo "Two canonical excision squares: only existing B-I plus standard three axioms."
end

assert_two_canonical_excision_Tor_dependencies
