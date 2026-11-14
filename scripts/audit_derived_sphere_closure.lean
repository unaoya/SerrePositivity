import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.SphereClosureInput
import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereClosureSemifreeCovers
import Lean
/-! sphere-only 模型の D-1 telescope 被覆の全宣言を監査する。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereClosurePerfectCovers,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereClosureComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SphereClosureConeInput,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.SphereClosureInput,

    `SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereClosureFamily,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereClosureOperations,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereClosurePretriangulated,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereClosureImage,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereClosureRetract,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereClosureGradedExtension,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereClosureSemifreeCovers]
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

#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_smallSemifreeRetractCovers
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_homotopyRetractCovers
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_smallSemifreeCovers

#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_perfectCovers
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosure_covers_unconditional
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional'
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput_unconditional'
