import SerrePositivity.InfinityCategories.F2.Ind
import Lean.Util.CollectAxioms

/-!
概要：F2N-2 の独立集約に属する全宣言の公理依存を監査する。
方針：所有モジュールの接頭辞で生成宣言も抽出し、再帰的に公理を確認する。
規約：許す公理は propext・Classical.choice・Quot.sound のみ。
使われ方：Ind の検証済み区切りの保存前に実行する。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless `SerrePositivity.InfinityCategories.F2.Ind |>.isPrefixOf mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "F2 Ind: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "F2 Ind: no declarations audited"
  logInfo m!"F2 Ind audit passed: {count} declarations, standard three axioms only."

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafElementsYonedaDiagram
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafElementsYonedaDiagram_vertex
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafElementsColimitCocone_isColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafElementsColimitCocone_evaluation
#check @SerrePositivity.InfinityCategories.F2.IsKappaFiltered
#check @SerrePositivity.InfinityCategories.F2.Ind.isIndVertex_kappaColimitClosed
#check @SerrePositivity.InfinityCategories.F2.Ind.isIndVertex_minimal
#check @SerrePositivity.InfinityCategories.F2.Ind.IndInfinity
#check @SerrePositivity.InfinityCategories.F2.Ind.indInclusionPresheaf_isFullyFaithful
#check @SerrePositivity.InfinityCategories.F2.Ind.indYoneda_inclusion
#check @SerrePositivity.InfinityCategories.F2.Ind.indYoneda_isFullyFaithful
