import SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.All
import SerrePositivity.InfinityCategories.Derived.SuspensionAction.All
import Lean
/-! D-S の所有する新規葉の全宣言について、未証明入力と追加公理を排除する。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.ChoiceInvariant,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.CellGenerators,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.ContractionComparison,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.StrictRange,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.ExtensionRange,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.FamilyImage,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.FullFunctor,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.Comparison,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.Parameter,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.InputParameter,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.InputFunctor,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.NativeHom,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.ClosureFunctor,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.SphereFree,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.ModuleExtension,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.SphereClosure,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.Perfect,
    `SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.ImageLaws,
    `SerrePositivity.InfinityCategories.Derived.SuspensionAction.ConeData,
    `SerrePositivity.InfinityCategories.Derived.SuspensionAction.SphereConeData,
    `SerrePositivity.InfinityCategories.Derived.SuspensionAction.UnconditionalData,
    `SerrePositivity.InfinityCategories.Derived.SuspensionAction.QuotientParameter,
    `SerrePositivity.InfinityCategories.Derived.SuspensionAction.QuotientContractionComparison]
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
  logInfo m!"D-S closure audit passed: {total} declarations in {modules.size} modules."

#check SerrePositivity.InfinityCategories.dgModuleExtensionClosureFamilyImage
#check SerrePositivity.InfinityCategories.dgModuleExtensionClosureStrictImage
#check SerrePositivity.InfinityCategories.dgModuleExtensionClosureFunctor
#check SerrePositivity.InfinityCategories.dgKappaSphereFreeExtensionIso
#check SerrePositivity.InfinityCategories.dgModuleExtensionSphereCoproductIso
#check SerrePositivity.InfinityCategories.DGModuleStrictImage.id_functor
#check SerrePositivity.InfinityCategories.DGModuleStrictImage.comp_functor
#check SerrePositivity.InfinityCategories.DGModuleStrictImage.preservesPerfect
#check SerrePositivity.InfinityCategories.dgModuleStrictImageSuspensionMapData

#check SerrePositivity.InfinityCategories.dgKappaSphereClosureExtensionStrictImage
#check SerrePositivity.InfinityCategories.dgKappaSphereClosureExtensionFunctor

#check SerrePositivity.InfinityCategories.DGModuleStrictImage.comparisonIso
#check SerrePositivity.InfinityCategories.DGModuleStrictImage.comparison_naturality

#check SerrePositivity.InfinityCategories.dgKappaSphereClosureSuspensionMapData
#check SerrePositivity.InfinityCategories.dgKappaSphereClosureSuspensionInputMap

#check SerrePositivity.InfinityCategories.dgSuspensionUnconditionalMapData
#check SerrePositivity.InfinityCategories.dgKappaSphereClosureExtensionInputFunctor
#check SerrePositivity.InfinityCategories.dgKappaSphereClosureNativeHom

#check SerrePositivity.InfinityCategories.dgSuspensionQuotientParameter
#check SerrePositivity.InfinityCategories.dgSuspensionQuotientParameter_epsilon_necessary

#check SerrePositivity.InfinityCategories.dgGradedContractionPrimitive_d
#check SerrePositivity.InfinityCategories.dgGradedContractionPrimitive_map
#check SerrePositivity.InfinityCategories.dgSuspensionContractionCorrection_d

#check SerrePositivity.InfinityCategories.dgCellCycleSphere_comparison
#check SerrePositivity.InfinityCategories.dgCellComparisonHom_initialNaturality_mapped

#check SerrePositivity.InfinityCategories.dgCellComparisonHom_unitGeneratorNaturality
#check SerrePositivity.InfinityCategories.dgProjectiveClosureFamilyImage_index_eq_of_iso
#check SerrePositivity.InfinityCategories.dgProjectiveClosureFunctor_obj_eq_of_iso
