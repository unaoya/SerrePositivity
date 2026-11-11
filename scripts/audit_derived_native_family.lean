import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ConeDerivedEquivalence
import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.SphereClosureCompactComparison
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionFixedCoherenceTypes
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionFixedStrictLaws
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionConeComparisonCore
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionConeRepresentativeComparison
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionModuleCompositionIso
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionUnitConeComparison
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionCompositionConeComparison
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SphereClosureEdgeIsoAdapter
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SphereClosureKernelHom
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SphereClosureNativeComparison
import Lean
/-! 実構成した実 Morita／P/Yoneda 全入力族の全宣言を監査する。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaNativeMoritaFamily,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaNativePFamily,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SphereClosureNativeComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SphereClosureKernelMap,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeFullRestriction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ConeDerivedEquivalence,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.SphereClosureCompactComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionFixedCoherenceTypes,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionFixedStrictLaws,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionConeComparisonCore,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionConeRepresentativeComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionModuleCompositionIso,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionUnitConeComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionCompositionConeComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeMappingVertexEdge,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SphereClosureQuotientEdge,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SphereClosureEdgeIsoAdapter,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SphereClosureKernelHom]
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
  logInfo m!"D native family audit passed: {total} declarations in {modules.size} modules."

#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaFamily
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaFamily_source
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaFamily_at
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaFamily_iso
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePComparisonFamily
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePArrowFamily_boundary
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePComparisonFamily_at
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativePComparisonFamily_iso

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSphereClosureKernelInputMap
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSphereClosureKernelInputMap_inclusion
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSphereClosureSuspensionInputMap_projection
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSphereClosureNullInputMap_left

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgFullRestrictionFunctor
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgFullRestrictionNativeMap
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSuspensionKernelParameter
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaSuspensionKernelHom

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgNativeMappingVertexEdge
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionQuotientNativeEdge_eq
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionQuotientNativeEdgeIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionEdgeIsoOfQuotientComparison
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionEdgeIsoOfQuotientEdgeEq

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGSuspensionFixedUnitComparison
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGSuspensionFixedCompositionComparison

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionFixedUnitInputEqOfConeEq
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionFixedCompositionInputEqOfConeEq
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionConeRepresentativeIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionUnitConeEvaluationIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionCompositionConeEvaluationIso

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeCompactComparison_inclusion
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeCompactEquivalence_inverse_inclusion
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaSphereClosureCompactEquivalence
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaSphereClosureCompactEquivalence_hom
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaSphereClosureCountableSum_isExactFunctor
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaSphereClosureSwindleInfinityIso
