import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.All
import Lean.Util.CollectAxioms

/-!
概要：P-d の accessible 引き戻し所有宣言を再帰的に公理監査する。
方針：所有モジュールの宣言を列挙し、その全公理依存を検査する。
規約：propext・Classical.choice・Quot.sound だけを許す。
使われ方：AccessiblePullback.All のビルド後の専用監査。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback).isPrefixOf mod do
      continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Accessible pullback: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Accessible pullback: no declarations audited"
  logInfo m!"Accessible pullback audit passed: {count} declarations, standard three axioms only."

#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.exists_relativeCardinals
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.chainUnion_isCardinalFiltered
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.chainUnionPiece
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ordinalNerve_isKappaFiltered
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ordinalChainUnionPiece
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.exists_partialColimit_compact_image
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.alternatingIndex_isCardinalFiltered
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.alternatingSection_isRightCofinal
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.HasComponentPresentations
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.isKappaAccessible_of_componentPresentations
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.isPresentable_of_isAccessible

#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.fullCosliceRestrictionIso_hom_inclusion
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.indInclusion_preservesCompact
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.exists_presheafEmbedding
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.exists_factorizationEdge_of_isPullback
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.compactDiagram_factorization_of_fullSubcomplex

#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.cosliceEndpointMap_trivialKanFibration
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.compactDiagram_factorization_ind
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.trivialKan_exists_edge_target
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.exists_factorizationEdge_of_trivialKan
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.compactDiagramFactorization_of_isKappaAccessible
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.alternatingIndex_hasCardinalLT
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.alternatingNerve_isKappaSmall
#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.exists_alternatingColimit_compact_image

#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.exists_chainGluing

#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.alternatingColimit_vertexIso

#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.isKappaCompact_smallSourceCosliceVertex

#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.compactDiagram_factorization_relative_smallPrefix

#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.compactDiagram_factorization_relative_fullSubcomplex

#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.smallPrefix_cosliceProjection_isRightCofinal

#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.compactDiagram_factorization_relative_ind

#check @SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.compactDiagram_factorization_over_smallPrefixPresentation_ind
