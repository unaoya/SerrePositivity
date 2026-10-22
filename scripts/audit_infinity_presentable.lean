import SerrePositivity.InfinityCategories.F2.Presentable
import Lean.Util.CollectAxioms

/-!
P レーンの所有モジュールの全宣言について、再帰的に公理依存を検査する。
許す公理は propext・Classical.choice・Quot.sound のみ。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless `SerrePositivity.InfinityCategories.F2.Presentable |>.isPrefixOf mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Presentable: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Presentable: no declarations audited"
  logInfo m!"Presentable audit passed: {count} declarations, standard three axioms only."

#check @SerrePositivity.InfinityCategories.F2.Presentable.IsKappaAccessible
#check @SerrePositivity.InfinityCategories.F2.Presentable.IsAccessible
#check @SerrePositivity.InfinityCategories.F2.Presentable.IsKappaAccessibleFunctor
#check @SerrePositivity.InfinityCategories.F2.Presentable.indInfinity_isKappaAccessible
#check @SerrePositivity.InfinityCategories.F2.Presentable.IsKappaCompactGenerating.compact_iff_retract
#check @SerrePositivity.InfinityCategories.F2.Presentable.IsKappaAccessible.exists_indComparison
#check @SerrePositivity.InfinityCategories.F2.Presentable.indComparison_isEssentiallySurjective
#check @SerrePositivity.InfinityCategories.F2.Presentable.indComparison_generator_pinchedHomMap_isEquivalence
