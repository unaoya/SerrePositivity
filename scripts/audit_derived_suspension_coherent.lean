import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.DGSuspensionCoherentSquareInput
import Lean
/-! 採用 B1 の作用・全四角形入力の全宣言を監査する。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.DGSuspensionCoherentActionInput,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.DGSuspensionCoherentSquareInput]
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
  logInfo m!"D coherent input audit passed: {total} declarations in {modules.size} modules."

#check SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput.ofStrict
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentSquareInput
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentSquareInput.ofStrict
