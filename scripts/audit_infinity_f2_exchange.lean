import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedRightFamilyFixedEvaluation
import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedValueFamilyTwoStage
import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexTwoEvaluationCriterion
import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroMorphismCoherence
import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentSimplexAppendMorphism
import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentSimplexLastPostComposition
import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCompositionPrismPost
import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentRightSlicePostComposition
import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentHomSlicePost
import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentRightSlicePostFiber
import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionFiberWitnessPost
import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalPrismPostNaturality
import Lean.Util.CollectAxioms

/-!
X レーン専用。既存の audit_infinity_f2 は変更しない。
読み込んだ FilteredExchange の宣言（生成宣言を含む）を宣言元で選別し、
依存公理を再帰的に監査する。未完の Ncomp・一般交換の完了は主張しない。
-/

#check @SerrePositivity.InfinityCategories.F2.pointedRightFamilyEvaluation_const
#check @SerrePositivity.InfinityCategories.F2.pointedRightFamilyEvaluation_const_comp
#check @SerrePositivity.InfinityCategories.F2.pointedRightFamilyEvaluationValueIso_const_heq
#check @SerrePositivity.InfinityCategories.F2.pointedValueFamilyTwoStageIso
#check @SerrePositivity.InfinityCategories.F2.pointedValueFamilyCompositeIso
#check @SerrePositivity.InfinityCategories.F2.coherentColimitApexZeroCompositeValue_heq_two_evaluation
#check @SerrePositivity.InfinityCategories.F2.coherentColimitApexZeroCompositeValue_heq_composite_iff
#check @SerrePositivity.InfinityCategories.F2.coherentColimitApexZeroCompositeValue_heq_triangle_iff
#check @SerrePositivity.InfinityCategories.F2.coherentSimplexLastPost
#check @SerrePositivity.InfinityCategories.F2.coherentSimplexLastPost_old_face
#check @SerrePositivity.InfinityCategories.F2.coherentSimplexLastPost_comp
#check @SerrePositivity.InfinityCategories.F2.coherentSimplexAppendMorphism
#check @SerrePositivity.InfinityCategories.F2.coherentSimplexAppendMorphism_face_last
#check @SerrePositivity.InfinityCategories.F2.coherentCompositionSimplex_last_post
#check @SerrePositivity.InfinityCategories.F2.coherentSimplexLastPost_reindex
#check @SerrePositivity.InfinityCategories.F2.coherentRightSlicePost
#check @SerrePositivity.InfinityCategories.F2.coherentRightSlicePost_projection
#check @SerrePositivity.InfinityCategories.F2.coherentRightSlicePost_comp
#check @SerrePositivity.InfinityCategories.F2.coherentCompositionPrism_post
#check @SerrePositivity.InfinityCategories.F2.coherentHomSliceComparison_post
#check @SerrePositivity.InfinityCategories.F2.coherentRightSlicePostFiber_comp
#check @SerrePositivity.InfinityCategories.F2.coherentHomSliceFiberComparison_post
#check @SerrePositivity.InfinityCategories.F2.relativeExtensionPost_vertex
#check @SerrePositivity.InfinityCategories.F2.relativeExtensionFiberEndpoint_post
#check @SerrePositivity.InfinityCategories.F2.relativeExtensionFiberComparison_post
#check @SerrePositivity.InfinityCategories.F2.relativeExtensionFiberEndpoint_witnessIso_post
#check @SerrePositivity.InfinityCategories.F2.leftFibrationPrism_diagonalTransportIso_post

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless `SerrePositivity.InfinityCategories.F2.FilteredExchange |>.isPrefixOf mod do
      continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "FilteredExchange: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "FilteredExchange: no declarations audited"
  logInfo m!"FilteredExchange audit passed: {count} declarations, standard three axioms only."
