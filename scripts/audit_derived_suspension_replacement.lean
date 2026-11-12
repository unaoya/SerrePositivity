import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionNativeSquareReplacement
import Lean
/-! 元の全四角形を回収する相対延長：全宣言を三公理以内で監査する。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.NativeDiagramFamilyReplacement,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionNativeSquareReplacement]
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
  logInfo m!"D suspension replacement audit passed: {counts.foldl (· + ·) (0 : Nat)} declarations in {modules.size} modules."

#check SerrePositivity.InfinityCategories.Project.DerivedCategories.nativeDiagramFamily_relativeReplacement
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.nativeDiagramFamily_exists_replacement
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSuspensionNativeSquare_exists_replacement
