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
