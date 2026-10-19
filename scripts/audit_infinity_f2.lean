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
#check @SerrePositivity.InfinityCategories.F2.catPullbackObject
#check @SerrePositivity.InfinityCategories.F2.catPullbackCommutativity
#check @SerrePositivity.InfinityCategories.F2.catPullbackLift
#check @SerrePositivity.InfinityCategories.F2.catPullback_hom_ext
#check @SerrePositivity.InfinityCategories.F2.catPullbackFunctorIso
#check @SerrePositivity.InfinityCategories.F2.pullback_isInvertibleEdge_iff
#check @SerrePositivity.InfinityCategories.F2.corePullbackIso
#check @SerrePositivity.InfinityCategories.F2.catPullbackFunctorCoreIso
#check @SerrePositivity.InfinityCategories.F2.catPullbackFunctorCoreIso_fst
#check @SerrePositivity.InfinityCategories.F2.catPullbackFunctorCoreIso_snd
#check @SerrePositivity.InfinityCategories.F2.coreMap_trivialKanFibration
#check @SerrePositivity.InfinityCategories.F2.corePathReplacementProjection_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.coreMap_rightFibration_of_invertibleTargetLifting
#check @SerrePositivity.InfinityCategories.F2.corePathReplacementMap_fibration
#check @SerrePositivity.InfinityCategories.F2.corePathReplacementMap_internalHom_fibration
#check @SerrePositivity.InfinityCategories.F2.qCatHom_postcomp
#check @SerrePositivity.InfinityCategories.F2.qCatPullbackHomIso
#check @SerrePositivity.InfinityCategories.F2.qCatPullbackHomCone_isLimit
#check @SerrePositivity.InfinityCategories.F2.qCatPullbackInfinityCone_isLimit
#check @SerrePositivity.InfinityCategories.F2.catPullbackReplacementCone_isLimit
#check @SerrePositivity.InfinityCategories.F2.catPullbackReplacementCone_vertex
#check @SerrePositivity.InfinityCategories.F2.strictCoherentNatTransMap_zero
#check @SerrePositivity.InfinityCategories.F2.strictCoherentNatTransMap_one
#check @SerrePositivity.InfinityCategories.F2.strictCoherentNatTransMap_component
#check @SerrePositivity.InfinityCategories.F2.strictCoherentNatTransIso
#check @SerrePositivity.InfinityCategories.F2.catPullbackDiagram
#check @SerrePositivity.InfinityCategories.F2.catPullbackReplacementNatTrans_isEquivalence
#check @SerrePositivity.InfinityCategories.F2.catPullbackReplacementDiagramIso
#check @SerrePositivity.InfinityCategories.F2.sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence
#check @SerrePositivity.InfinityCategories.F2.exists_limitCone_extension_of_precompositionEquivalence
#check @SerrePositivity.InfinityCategories.F2.exists_limitCone_of_functorIso
#check @SerrePositivity.InfinityCategories.F2.catPullbackCone_isLimit
#check @SerrePositivity.InfinityCategories.F2.catPullbackCone_vertex
#check @SerrePositivity.InfinityCategories.F2.catPullbackDiagram_hasLimit
