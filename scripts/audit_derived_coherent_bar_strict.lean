import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.All
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Diagram,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.FilteredExactness,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationGraded,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Columns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ComplexColimit,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendSimplex,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationColumns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ZeroShift,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Edge,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ShiftPostcomposition,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationEdge,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ModuleColimit,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.EdgeObjects,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.EdgeCoefficients,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendColumn,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationTheta,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendClosed,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomExchange,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.FiniteBounds,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.NormalizedEndRebase]
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
  logInfo m!"D-e strict bar audit passed: {count} declarations in {seen.size} modules."

#check SerrePositivity.InfinityCategories.dgCoherentBarStrictDiagram
#check SerrePositivity.InfinityCategories.dgCoherentBarStrictNormalizedModule
#check SerrePositivity.InfinityCategories.dgCoherentBarStrictAugmentationGraded
#check SerrePositivity.InfinityCategories.dgStrictFilteredColimit_quasiIso

#check SerrePositivity.InfinityCategories.dgStrictFilteredModuleColimit_quasiIso
#check SerrePositivity.InfinityCategories.dgCoherentBarStrictAugmentation_postNormalizedTheta
#check SerrePositivity.InfinityCategories.dgStrictAppendHom
#check SerrePositivity.InfinityCategories.dgStrictNormalizedDegree_finiteSupport
