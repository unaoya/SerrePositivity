import SerrePositivity.InfinityCategories.F2
import Lean.Util.CollectAxioms

/-!
概要：F2 の公開宣言と生成宣言の依存公理を検査する。
方針：宣言元モジュールを判別し、各宣言の公理を再帰的に収集する。
規約：許す公理は propext・Classical.choice・Quot.sound のみ。
使われ方：F2 の保存単位の対象ビルド後の公理監査。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless `SerrePositivity.InfinityCategories.F2 |>.isPrefixOf mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "F2: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "F2: no declarations audited"
  logInfo m!"F2 audit passed: {count} declarations, standard three axioms only."

#check @SerrePositivity.InfinityCategories.F2.coherentVertexEquiv
#check @SerrePositivity.InfinityCategories.F2.catInfinityVertexEquiv
#check @SerrePositivity.InfinityCategories.F2.coherentOrderDiagram
#check @SerrePositivity.InfinityCategories.F2.coherentEdgeHom_edge
#check @SerrePositivity.InfinityCategories.F2.coherentEdge_source
#check @SerrePositivity.InfinityCategories.F2.coherentEdge_target
#check @SerrePositivity.InfinityCategories.F2.coherentEdge_recover
#check @SerrePositivity.InfinityCategories.F2.coherentEdgeEquiv
#check @SerrePositivity.InfinityCategories.F2.catInfinityEdgeEquiv
#check @SerrePositivity.InfinityCategories.F2.coherentEdge_id
#check @SerrePositivity.InfinityCategories.F2.coherentCompStruct
#check @SerrePositivity.InfinityCategories.F2.catInfinityMappingEquivalence
#check @SerrePositivity.InfinityCategories.F2.catInfinityMappingEquivalence_hom
#check @SerrePositivity.InfinityCategories.F2.catInfinityMappingComparison_ordinary
#check @SerrePositivity.InfinityCategories.F2.catInfinityMappingComparison_enriched_naturality
#check @SerrePositivity.InfinityCategories.F2.catInfinity_homMk_eq_iff_functorIso
#check @SerrePositivity.InfinityCategories.F2.catInfinityEdge_isInvertible_iff
