import SerrePositivity.InfinityCategories.Derived.KappaPerfect.SphereClosureInput
import SerrePositivity.InfinityCategories.Derived.DGKappaSphereClosureSemifreeCovers
import Lean
/-! sphere-only 模型の D-1 telescope 被覆の全宣言を監査する。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.InfinityCategories.Derived.DGKappaSphereClosurePerfectCovers,
    `SerrePositivity.InfinityCategories.Derived.DGKappaSphereClosureComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SphereClosureConeInput,
    `SerrePositivity.InfinityCategories.Derived.KappaPerfect.SphereClosureInput,

    `SerrePositivity.InfinityCategories.Derived.DGKappaSphereClosureFamily,
    `SerrePositivity.InfinityCategories.Derived.DGKappaSphereClosureOperations,
    `SerrePositivity.InfinityCategories.Derived.DGKappaSphereClosurePretriangulated,
    `SerrePositivity.InfinityCategories.Derived.DGKappaSphereClosureImage,
    `SerrePositivity.InfinityCategories.Derived.DGKappaSphereClosureRetract,
    `SerrePositivity.InfinityCategories.Derived.DGKappaSphereClosureGradedExtension,
    `SerrePositivity.InfinityCategories.Derived.DGKappaSphereClosureSemifreeCovers]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut counts : Array Nat := modules.map (fun _ => 0)
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.header.modules[index.toNat]!.module
    let some position := modules.idxOf? moduleName | continue
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "Forbidden axiom {dependency} in {name}"
    counts := counts.modify position (· + 1)
  for position in [:modules.size] do
    unless counts[position]! > 0 do
      throwError "No declarations checked in {modules[position]!}"
  let total := counts.foldl (· + ·) (0 : Nat)
  logInfo m!"D sphere closure audit passed: {total} declarations in {modules.size} modules."

#check SerrePositivity.InfinityCategories.dgKappaSphereClosureObjects_smallSemifreeRetractCovers
#check SerrePositivity.InfinityCategories.dgKappaSphereClosureObjects_homotopyRetractCovers
#check SerrePositivity.InfinityCategories.dgKappaSphereClosureObjects_smallSemifreeCovers

#check SerrePositivity.InfinityCategories.dgKappaSphereClosureObjects_perfectCovers
#check SerrePositivity.InfinityCategories.dgKappaSphereClosure_covers_unconditional
#check SerrePositivity.InfinityCategories.dgKappaConeInput_unconditional'
#check SerrePositivity.InfinityCategories.dgKappaPerfectInput_unconditional'
