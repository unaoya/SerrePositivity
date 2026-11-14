import SerrePositivity.InfinityCategories.Project.Entrypoints.F2PresentableLocalizationLocalObjectsAll
import Lean.Util.CollectAxioms

/-!
概要：P-d の局所対象圏の所有宣言を再帰的に公理監査する。
方針：所有モジュールから導入された全宣言の公理依存を列挙する。
規約：propext・Classical.choice・Quot.sound のみを許す。
使われ方：LocalObjects.All の専用ビルド後の検証。
-/

open Lean in
run_cmd do
  let oldAuditPrefix1 := `SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects
  let klw1AuditLayout1 ← IO.ofExcept <| Lean.Json.parse (← IO.FS.readFile "scripts/refactor/targets/bulk-kl-module-map.json")
  let klw1AuditLayout1 ← IO.ofExcept klw1AuditLayout1.getObj?
  let klw1AuditOwners1 := Std.HashSet.ofList (klw1AuditLayout1.toList.filterMap fun (source, dest) =>
    if oldAuditPrefix1.isPrefixOf source.toName then dest.getStr?.toOption.map String.toName else none)
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (oldAuditPrefix1.isPrefixOf mod || klw1AuditOwners1.contains mod) do
      continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Presentable local objects: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Presentable local objects: no declarations audited"
  logInfo m!"Presentable local objects audit passed: {count} declarations, standard three axioms only."

#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Definition.Category
#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isAccessible
#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Definition.isLocalObject_range_iff
#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_iff_representableInverts
#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localPrecompositionComparison_isIso_iff
#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_colimit_of_compactEndpoints
#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalObject_colimit_of_compactEndpoints
#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasSmallKappaFilteredColimits
#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.inclusion_isKappaAccessibleFunctor
#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_inclusion_accessibilityCardinal
#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reflectiveSubcategory_isKappaAccessible
#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasSmallColimits_of_reflection
#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isAccessible_of_reflection
#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_of_reflection
#check @SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_of_localReplacements
