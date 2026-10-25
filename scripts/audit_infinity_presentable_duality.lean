import SerrePositivity.InfinityCategories.F2.Presentable.Duality.All
import Lean.Util.CollectAxioms

/-!
概要：P-d の所有する全宣言の再帰的公理依存を監査する。
方針：Duality 名前空間のモジュールから導入された宣言を列挙する。
規約：propext・Classical.choice・Quot.sound だけを許す。
使われ方：Duality.All のビルド後の独立監査。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.InfinityCategories.F2.Presentable.Duality).isPrefixOf mod do
      continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Presentable duality: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Presentable duality: no declarations audited"
  logInfo m!"Presentable duality audit passed: {count} declarations, standard three axioms only."

#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftVertex_exists_rightAdjoint
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightVertex_exists_leftAdjoint
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.chosenRightAdjunction
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.chosenLeftAdjunction
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.chosenRightAdjoint_condition
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.chosenLeftAdjoint_condition
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightAdjointVertex
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftAdjointVertex
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftRoundtripIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightRoundtripIso
