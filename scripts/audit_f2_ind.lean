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

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafYonedaSlice

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafYonedaSliceProjection

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafYonedaSliceDiagram

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafYonedaSliceCocone

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafYonedaSliceCocone_vertex

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafYonedaSliceFiberMappingIso

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafYonedaSliceFiberValueEquivalence

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafElementsCoconeOfComparison

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafElementsCoconeOfComparison_vertex

#check @SerrePositivity.InfinityCategories.F2.Ind.isColimitCone_of_fullInclusion
#check @SerrePositivity.InfinityCategories.F2.Ind.fullCoconeLift_inclusion
#check @SerrePositivity.InfinityCategories.F2.Ind.ind_exists_colimitCone
#check @SerrePositivity.InfinityCategories.F2.Ind.ind_hasColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.ind_isColimit_iff_inclusion

#check @SerrePositivity.InfinityCategories.F2.Ind.edgewiseRightExtensionDomain_rightAnodyne
#check @SerrePositivity.InfinityCategories.F2.Ind.edgewiseRightWeightDomain_relative_lift
#check @SerrePositivity.InfinityCategories.F2.Ind.relativeEdgewiseRightComparison_trivialKanFibration
#check @SerrePositivity.InfinityCategories.F2.Ind.twistedArrowRightSection_comparison
#check @SerrePositivity.InfinityCategories.F2.Ind.twistedArrowSourceLift_projection
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafTwistedElementsEvaluation
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafTwistedElementsEvaluation_projection

#check @SerrePositivity.InfinityCategories.F2.Ind.twistedElementsBaseChangeIso
#check @SerrePositivity.InfinityCategories.F2.Ind.twistedElementsReconstruction_isPrecompositionEquivalence
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityJointHomotopy
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityDiagramHomotopy
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityCoconeRealization
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityCocone_vertex
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafElementsYonedaSliceComparison_projection
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafElementsYonedaSliceComparison_cocone

#check @SerrePositivity.InfinityCategories.F2.Ind.edgewiseVertexFiberLift_map
#check @SerrePositivity.InfinityCategories.F2.Ind.twistedIdentityFiberEvaluation_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Ind.twistedSourceElementsIdentityInclusion_isWeakHomotopyEquivalence
#check @SerrePositivity.InfinityCategories.F2.Ind.twistedSourceElementsComparison_identity
#check @SerrePositivity.InfinityCategories.F2.Ind.twistedSourceElementsEvaluation_identity
#check @SerrePositivity.InfinityCategories.F2.Ind.twistedSourceElementsEvaluation_isWeakHomotopyEquivalence

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityRecoveredHomotopy_h
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityCoconeTransformationIso
#check @SerrePositivity.InfinityCategories.F2.Ind.coconeTransformationPointAt_post
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityEvaluationCoconeTransformationIso
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityEvaluatedFiberMap_vertex
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityEvaluationFiberIso
