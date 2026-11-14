import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGSuspensionNativeNaturalityModel
import Lean
/-! 同じ P/Yoneda 比較と全入力への相対延長の全新規宣言を監査する。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.NativeArrowRelativeComparison,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaNativePComparison,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGSuspensionNativeNaturalityModel]
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
  logInfo m!"D native P audit passed: {counts.foldl (· + ·) (0 : Nat)} declarations in {modules.size} modules."

#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePFamily_exists
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionNativeNaturalityModel
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionNativeNaturalityModel.perfectFamily
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionNativeNaturalityModel.perfectComparison_at
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionNativeNaturalityModel.perfectFamily_boundary

#check SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionNativeNaturalityModel.moritaIso
