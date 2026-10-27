import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ConeDerivedEquivalence
import SerrePositivity.InfinityCategories.Derived.KappaPerfect.SphereClosureCompactComparison
import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionFixedCoherenceTypes
import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionFixedStrictLaws
import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionConeComparisonCore
import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionConeRepresentativeComparison
import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionModuleCompositionIso
import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionUnitConeComparison
import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionCompositionConeComparison
import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SphereClosureEdgeIsoAdapter
import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SphereClosureKernelHom
import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SphereClosureNativeComparison
import Lean
/-! 実構成した実 Morita／P/Yoneda 全入力族の全宣言を監査する。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.InfinityCategories.Derived.DGKappaNativeMoritaFamily,
    `SerrePositivity.InfinityCategories.Derived.DGKappaNativePFamily,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SphereClosureNativeComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SphereClosureKernelMap,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeFullRestriction,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ConeDerivedEquivalence,
    `SerrePositivity.InfinityCategories.Derived.KappaPerfect.SphereClosureCompactComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionFixedCoherenceTypes,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionFixedStrictLaws,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionConeComparisonCore,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionConeRepresentativeComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionModuleCompositionIso,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionUnitConeComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SuspensionCompositionConeComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeMappingVertexEdge,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SphereClosureQuotientEdge,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SphereClosureEdgeIsoAdapter,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SphereClosureKernelHom]
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

#check SerrePositivity.InfinityCategories.dgKappaNativeMoritaFamily
#check SerrePositivity.InfinityCategories.dgKappaNativeMoritaFamily_source
#check SerrePositivity.InfinityCategories.dgKappaNativeMoritaFamily_at
#check SerrePositivity.InfinityCategories.dgKappaNativeMoritaFamily_iso
#check SerrePositivity.InfinityCategories.dgKappaNativePComparisonFamily
#check SerrePositivity.InfinityCategories.dgKappaNativePArrowFamily_boundary
#check SerrePositivity.InfinityCategories.dgKappaNativePComparisonFamily_at
#check SerrePositivity.InfinityCategories.dgKappaNativePComparisonFamily_iso

#check SerrePositivity.InfinityCategories.dgKappaSphereClosureKernelInputMap
#check SerrePositivity.InfinityCategories.dgKappaSphereClosureKernelInputMap_inclusion
#check SerrePositivity.InfinityCategories.dgKappaSphereClosureSuspensionInputMap_projection
#check SerrePositivity.InfinityCategories.dgKappaSphereClosureNullInputMap_left

#check SerrePositivity.InfinityCategories.dgFullRestrictionFunctor
#check SerrePositivity.InfinityCategories.dgFullRestrictionNativeMap
#check SerrePositivity.InfinityCategories.dgKappaSuspensionKernelParameter
#check SerrePositivity.InfinityCategories.dgKappaSuspensionKernelHom

#check SerrePositivity.InfinityCategories.dgNativeMappingVertexEdge
#check SerrePositivity.InfinityCategories.dgSuspensionQuotientNativeEdge_eq
#check SerrePositivity.InfinityCategories.dgSuspensionQuotientNativeEdgeIso
#check SerrePositivity.InfinityCategories.dgSuspensionEdgeIsoOfQuotientComparison
#check SerrePositivity.InfinityCategories.dgSuspensionEdgeIsoOfQuotientEdgeEq

#check SerrePositivity.InfinityCategories.DGSuspensionFixedUnitComparison
#check SerrePositivity.InfinityCategories.DGSuspensionFixedCompositionComparison

#check SerrePositivity.InfinityCategories.dgSuspensionFixedUnitInputEqOfConeEq
#check SerrePositivity.InfinityCategories.dgSuspensionFixedCompositionInputEqOfConeEq
#check SerrePositivity.InfinityCategories.dgSuspensionConeRepresentativeIso
#check SerrePositivity.InfinityCategories.dgSuspensionUnitConeEvaluationIso
#check SerrePositivity.InfinityCategories.dgSuspensionCompositionConeEvaluationIso

#check SerrePositivity.InfinityCategories.dgKappaConeCompactComparison_inclusion
#check SerrePositivity.InfinityCategories.dgKappaConeCompactEquivalence_inverse_inclusion
#check SerrePositivity.InfinityCategories.dgKappaSphereClosureCompactEquivalence
#check SerrePositivity.InfinityCategories.dgKappaSphereClosureCompactEquivalence_hom
#check SerrePositivity.InfinityCategories.dgKappaSphereClosureCountableSum_isExactFunctor
#check SerrePositivity.InfinityCategories.dgKappaSphereClosureSwindleInfinityIso
