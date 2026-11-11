import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonNativeComposition
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonFamilyLift
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonNative
import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonCriterion
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientParameterLaws

import Lean
/-! 固定実商の全パラメータ延長の全新規宣言：許容三公理のみ。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonFamilyLift,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonNative,
    `SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonHorizontal,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonHorizontalFunctor,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonNativeComposition,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonHom,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonCategory,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonCriterion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientParameterLaws,
    `SerrePositivity.DifferentialGraded.Functor.ModuleValued,
    `SerrePositivity.DifferentialGraded.Quotient.Path.Construction,
    `SerrePositivity.DifferentialGraded.Quotient.Path.Evaluation]
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
  logInfo m!"D quotient parameter audit passed: {counts.foldl (· + ·) (0 : Nat)} declarations in {modules.size} modules."

#check SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension
#check SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension_exists_iff
#check SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension_reindex
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension_exists_iff

#check SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension_postcomposition
#check SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension_postcomposition_heq

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.parameterExtension_identity
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.parameterExtension_composition

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientInputFunctor
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientInputFunctor_obj
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom_factor_iff

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonNativeForget
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonNativeMap_vertex
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonNativeMap_unit
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonNativeMap_composition
