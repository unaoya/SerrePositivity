import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCellProjectiveInput
import Lean
/-! 固定 cell graph 射影性の全新規宣言：許容三公理のみ。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.DifferentialGraded.Complexes.TensorShift,
    `SerrePositivity.DifferentialGraded.Derived.Basic,
    `SerrePositivity.DifferentialGraded.Derived.BimoduleTensor,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.ComplexHomotopies.RingComplexColimits,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.ComplexHomotopies.ComplexProjectiveClosure,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.CellAttachments.DGCellAttachmentProjective,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.CellAttachments.DGCellSourceProjective,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.CellAttachments.DGCellResolvedGraphProjective,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCellProjectiveInput]
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
  logInfo m!"D cell projective audit passed: {counts.foldl (· + ·) (0 : Nat)} declarations in {modules.size} modules."

#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGluingCellRightAxisProjectiveInput
#print axioms SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGluingCellRightAxisProjectiveInput
