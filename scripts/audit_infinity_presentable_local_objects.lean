import SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.All
import Lean.Util.CollectAxioms

/-!
概要：P-d の局所対象圏の所有宣言を再帰的に公理監査する。
方針：所有モジュールから導入された全宣言の公理依存を列挙する。
規約：propext・Classical.choice・Quot.sound のみを許す。
使われ方：LocalObjects.All の専用ビルド後の検証。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects).isPrefixOf mod do
      continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Presentable local objects: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Presentable local objects: no declarations audited"
  logInfo m!"Presentable local objects audit passed: {count} declarations, standard three axioms only."

#check @SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.Category
#check @SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.isLocalObject_range_iff
#check @SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.isLocalForHom_iff_representableInverts
#check @SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.localPrecompositionComparison_isIso_iff
#check @SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.isLocalForHom_colimit_of_compactEndpoints
#check @SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.isLocalObject_colimit_of_compactEndpoints
#check @SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.hasSmallKappaFilteredColimits
#check @SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.inclusion_isKappaAccessibleFunctor
#check @SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.exists_regular_inclusion_accessibilityCardinal
#check @SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.reflectiveSubcategory_isKappaAccessible
#check @SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.hasSmallColimits_of_reflection
#check @SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.isAccessible_of_reflection
#check @SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.isPresentable_of_reflection
#check @SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.isPresentable_of_localReplacements
