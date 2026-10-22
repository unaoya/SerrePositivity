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
#check @SerrePositivity.InfinityCategories.F2.Presentable.covariantHomComparison
#check @SerrePositivity.InfinityCategories.F2.Presentable.cosliceComparisonOver_fiber_postcomp
#check @SerrePositivity.InfinityCategories.F2.Presentable.cosliceComparisonOver_fiber_equivalence_iff
#check @SerrePositivity.InfinityCategories.F2.Presentable.isFullyFaithful_iff_cosliceComparisonOver
#check @SerrePositivity.InfinityCategories.F2.Presentable.leftClassificationEdge_evaluation_square
#check @SerrePositivity.InfinityCategories.F2.Presentable.leftFibrationFiberEvaluation_original_edge
#check @SerrePositivity.InfinityCategories.F2.Presentable.indComparison_generator_cosliceFiber_isEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.covariantHomComparison_component_isIso_iff
#check @SerrePositivity.InfinityCategories.F2.Presentable.functorHomComparison_colimit_vertex
#check @SerrePositivity.InfinityCategories.F2.Presentable.pinchedHomMap_equivalence_of_compact_colimit
#check @SerrePositivity.InfinityCategories.F2.Presentable.indComparison_yoneda_pinchedHomMap_isEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.functorHomComparison_limit_vertex
#check @SerrePositivity.InfinityCategories.F2.Presentable.pinchedHomMap_equivalence_iff_op
#check @SerrePositivity.InfinityCategories.F2.Presentable.pinchedHomMap_equivalence_of_source_colimit
#check @SerrePositivity.InfinityCategories.F2.Presentable.indComparison_isFullyFaithful
#check @SerrePositivity.InfinityCategories.F2.Presentable.indComparisonEquivalence_hom
#check @SerrePositivity.InfinityCategories.F2.Presentable.IsKappaAccessible.exists_indRepresentation
#check @SerrePositivity.InfinityCategories.F2.Presentable.IsKappaAccessible.exists_indEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.equivalence_isColimitCone_iff
#check @SerrePositivity.InfinityCategories.F2.Presentable.covariantHomComparisonIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.isKappaCompact_iff_equivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.IsKappaCompactGenerating.of_equivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.isKappaAccessible_iff_equivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.isKappaAccessible_iff_indEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.isAccessible_iff_indEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.isAccessibleFunctor_iff_equivalence_conjugate
#check @SerrePositivity.InfinityCategories.F2.Presentable.exists_regular_cardinalChangeBound_family
#check @SerrePositivity.InfinityCategories.F2.Presentable.exists_smallFilteredPiece_containing
#check @SerrePositivity.InfinityCategories.F2.Presentable.smallFilteredPieces_nerve_isKappaFiltered
#check @SerrePositivity.InfinityCategories.F2.Presentable.smallFilteredPieces_cover
#check @SerrePositivity.InfinityCategories.F2.Presentable.smallFilteredPiece_nerve_properties
