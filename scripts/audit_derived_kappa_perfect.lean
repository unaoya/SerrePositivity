import SerrePositivity.InfinityCategories.Derived.KappaPerfect.All
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `SerrePositivity.InfinityCategories.Derived.KappaPerfect.Closure,
    `SerrePositivity.InfinityCategories.Derived.KappaPerfect.Equivalence,
    `SerrePositivity.InfinityCategories.Derived.KappaPerfect.Inclusion,
    `SerrePositivity.InfinityCategories.Derived.KappaPerfect.Input]
  let mut count := 0
  let mut seen : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    if info.isAxiom then throwError "New axiom: {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    if (info.type.find? fun e => match e with
      | .const n _ => n.getString! == "ModelCategory"
      | _ => false).isSome then
      throwError "ModelCategory assumption in {name}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"D-8 e axiom/signature audit passed: {count} declarations in {seen.size} modules."

#check SerrePositivity.InfinityCategories.dgKappaPerfectComparison
#check SerrePositivity.InfinityCategories.dgKappaPerfectComparison_isQCatEquivalence
#check SerrePositivity.InfinityCategories.dgKappaPerfectComparison_inclusionIso
#check SerrePositivity.InfinityCategories.dgKappaPerfectInput
