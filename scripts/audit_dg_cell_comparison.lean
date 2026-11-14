import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSuspensionCanonicalMapData
import Lean
/-! 固定 cell 比較の厳密則の全新規宣言：許容三公理のみ。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.DifferentialGraded.Resolution.Basic,
    `SerrePositivity.DifferentialGraded.Resolution.Cell,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSuspensionCanonicalMapData]
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
  logInfo m!"D cell comparison audit passed: {counts.foldl (· + ·) (0 : Nat)} declarations in {modules.size} modules."

#check SerrePositivity.DifferentialGraded.DGCategoryCellResolution.comparisonFunctor_identity
#check SerrePositivity.DifferentialGraded.DGCategoryCellResolution.comparisonFunctor_composition
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSuspensionMapDataOfCone_composition
#print axioms SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSuspensionMapDataOfCone_composition
