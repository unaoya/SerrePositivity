import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonCriterion
import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.QuotientParameterLaws
import SerrePositivity.DifferentialGraded.Quotient.ParameterPostcomposition
import Lean
/-! 固定実商の全パラメータ延長の全新規宣言：許容三公理のみ。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonCategory,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonCriterion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.QuotientParameterLaws,
    `SerrePositivity.DifferentialGraded.Quotient.ParameterPostcomposition,
    `SerrePositivity.DifferentialGraded.Functor.HomogeneousNaturality,
    `SerrePositivity.DifferentialGraded.Quotient.EpsilonHomogeneousExt,
    `SerrePositivity.DifferentialGraded.Quotient.HomogeneousNaturality,
    `SerrePositivity.DifferentialGraded.Quotient.ParameterExtension]
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

#check SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension_identity
#check SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension_composition

#check SerrePositivity.InfinityCategories.NullPreservingFunctorsε
#check SerrePositivity.InfinityCategories.quotientInputFunctor
#check SerrePositivity.InfinityCategories.quotientInputFunctor_obj
#check SerrePositivity.InfinityCategories.quotientEpsilonHom_factor_iff
