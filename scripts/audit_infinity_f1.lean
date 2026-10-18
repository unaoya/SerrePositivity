import SerrePositivity.InfinityCategories.F1
import Lean.Util.CollectAxioms

/-!
概要：F1 の全宣言の公理依存を監査する。
方針：宣言元モジュールで抽出し、生成宣言も含め再帰的に公理を調べる。
規約：許す公理は propext・Classical.choice・Quot.sound のみ。
使われ方：Kerodon §5.1 以降の各保存単位で対象ビルド後に実行する。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless `SerrePositivity.InfinityCategories.F1 |>.isPrefixOf mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "F1: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "F1: no declarations audited"
  logInfo m!"F1 audit passed: {count} declarations, standard three axioms only."

#check @SerrePositivity.InfinityCategories.IsCartesianEdge
#check @SerrePositivity.InfinityCategories.IsCocartesianEdge
#check @SerrePositivity.InfinityCategories.isCartesianEdge_of_rightFibration
#check @SerrePositivity.InfinityCategories.isCocartesianEdge_of_leftFibration
#check @SerrePositivity.InfinityCategories.IsCartesianEdge.comp
#check @SerrePositivity.InfinityCategories.IsCocartesianEdge.comp
#check @SerrePositivity.InfinityCategories.cartesianFibrations
#check @SerrePositivity.InfinityCategories.cocartesianFibrations
#check @SerrePositivity.InfinityCategories.CartesianFibration
#check @SerrePositivity.InfinityCategories.CocartesianFibration
#check @SerrePositivity.InfinityCategories.cartesianFibration_innerFibration
#check @SerrePositivity.InfinityCategories.cocartesianFibration_innerFibration
#check @SerrePositivity.InfinityCategories.rightFibration_cartesianFibration
#check @SerrePositivity.InfinityCategories.leftFibration_cocartesianFibration
#check @SerrePositivity.InfinityCategories.cartesianFibration_comp
#check @SerrePositivity.InfinityCategories.cocartesianFibration_comp
#check @SerrePositivity.InfinityCategories.vertexFiber_quasicategory_of_innerFibration
#check @SerrePositivity.InfinityCategories.isCartesianEdge_pullback
#check @SerrePositivity.InfinityCategories.isCocartesianEdge_pullback
#check @SerrePositivity.InfinityCategories.cartesianFibration_pullback_snd
#check @SerrePositivity.InfinityCategories.cocartesianFibration_pullback_snd
#check @SerrePositivity.InfinityCategories.rightFibration_of_cartesianFibration_of_all_edges
#check @SerrePositivity.InfinityCategories.rightFibration_iff_cartesianFibration_all_edges
#check @SerrePositivity.InfinityCategories.leftFibration_of_cocartesianFibration_of_all_edges
#check @SerrePositivity.InfinityCategories.leftFibration_iff_cocartesianFibration_all_edges
