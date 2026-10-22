import SerrePositivity.InfinityCategories.F2.Ind
import Lean.Util.CollectAxioms

#check @SerrePositivity.InfinityCategories.F2.Ind.isKappaSmall_iff_of_iso
#check @SerrePositivity.InfinityCategories.F2.Ind.isKappaSmall_range_of_mono
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_small_codiscreteConeRange
#check @SerrePositivity.InfinityCategories.F2.Ind.coneSimplexAppend_lastFace
#check @SerrePositivity.InfinityCategories.F2.Ind.coneLastFace_injective
#check @SerrePositivity.InfinityCategories.F2.Ind.isTerminalVertex_of_unique_lastFace
#check @SerrePositivity.InfinityCategories.F2.Ind.coneApex_isTerminalVertex
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_small_terminalSubcomplex
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalSubcomplexFamily_isCardinalFiltered
#check @SerrePositivity.InfinityCategories.F2.Ind.iSup_terminalSubcomplexFamily
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalSubcomplexFamilyCocone_isColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalCarrierCondition_map
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalCarrierCondition_of_boundary
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalCarrierValue_range_le
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalCarrierProjection_trivialKanFibration
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalCarrierRealization
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalCarrierRealization_range_le
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalSubcomplexRealization_vertex
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalSubcomplexRealization_range_le
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalSubcomplexBaseMap
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_pointJoinBoundary_extension_over_terminal
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_pointCosliceBoundary_lift_over_terminal
#check @SerrePositivity.InfinityCategories.F2.Ind.pointCoslice_terminalFiber_isContractibleKan
#check @SerrePositivity.InfinityCategories.F2.Ind.finite_join_of_finite
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_terminalSubcomplex_finite_bound
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_joinCocone_at_terminal
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_nerve_joinCocone_at_bound
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalCarrierLift_value
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalCarrierLift_projection
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_terminalSubcomplex_indexCocone
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_terminalSubcomplex_cosliceCone
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_terminalCarrier_cone_lift
#check @SerrePositivity.InfinityCategories.F2.Ind.nestedCosliceCocone_vertex
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_terminalCarrier_cosliceCone
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalCarrierCoslice_isFiltered
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalSubcomplexCarrierValue_isRightCofinal
#check @SerrePositivity.InfinityCategories.F2.Ind.isRightCofinal_section_of_trivialKanFibration
#check @SerrePositivity.InfinityCategories.F2.Ind.terminalSubcomplexBaseMap_isRightCofinal
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_cofinal_cardinalFiltered_poset
#check @SerrePositivity.InfinityCategories.F2.Ind.isKappaFiltered_nerve_of_cardinalFiltered
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_cofinal_kappaFiltered_poset

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
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensitySourceInclusion_source
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensitySourceInclusion_target
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityDiagramHomotopy_evaluation
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityEvaluatedTransformationVertex_restriction
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityJointRestriction_vertex
#check @SerrePositivity.InfinityCategories.F2.Ind.coherentMapRealizationLargeIso
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityEvaluationRelativeImageIso
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityLiftedEvaluationIso
#check @SerrePositivity.InfinityCategories.F2.Ind.twistedSourceElementsBaseChangeIso
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityEvaluationReconstruction_map
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityEvaluationReconstruction_isPrecompositionEquivalence
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityEvaluationReconstruction_realization
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityEvaluationGlobalComparisonIso
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityEvaluationConstantComparisonIso
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityEvaluationValueComparisonIso
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafRightFiberPointedIso_ι
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafRightFiberValueEquivalence_lift
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityRestrictedGlobalValueMap_factorization
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityRestrictedSmallValueMap_isWeakHomotopyEquivalence
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityEvaluationCocone_isColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityCocone_isColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityPresentation
#check @SerrePositivity.InfinityCategories.F2.Ind.isIndVertex_of_kappaFiltered_elements
#check @SerrePositivity.InfinityCategories.F2.Ind.HasKappaFilteredElements
#check @SerrePositivity.InfinityCategories.F2.Ind.hasKappaFilteredElements_isoClosed
#check @SerrePositivity.InfinityCategories.F2.Ind.hasKappaFilteredElements_yoneda
#check @SerrePositivity.InfinityCategories.F2.Ind.finiteGeneratorCocone_isColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.isCardinalPresentable_of_isKappaSmall
#check @SerrePositivity.InfinityCategories.F2.Ind.kappaSmall_relative_factorization_of_isColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_homotopy_at_stage_of_kappaFiltered_isColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.isKappaFiltered_of_strict_isColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.rightFibration_of_filtered_isColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightFibrationColimitProjection_ι
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightFibrationColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightFibrationColimit_isKappaFiltered
#check @SerrePositivity.InfinityCategories.F2.Ind.filteredFixedBaseColimit_isPullback
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightFibrationColimitFiberIso
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightFibrationFiberColimitCocone_ι
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightFibrationFiberColimitCocone_isColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.strictNativeCocone_isColimit_of_filtered_forget
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightFibrationFiberNativeCocone_isColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightFibrationFiberNativeCocone_vertex
#check @SerrePositivity.InfinityCategories.F2.Ind.edgewiseOrdinaryLift_rightFibrationOpposite
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightFibrationOppositeDiagramIso
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightStraighteningFiberDiagramIso
#check @SerrePositivity.InfinityCategories.F2.Ind.rightFibrationOppositeFiberDiagramIso
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightStraighteningOriginalFiberDiagramIso
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightStraighteningCocone
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightStraighteningCocone_vertex
#check @SerrePositivity.InfinityCategories.F2.Ind.coherentReturn_postcomp
#check @SerrePositivity.InfinityCategories.F2.Ind.strictNativeCocone_postcomp_val
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightFibrationOppositeCoconeIso
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightStraighteningColimitFiberCoconeIso
#check @SerrePositivity.InfinityCategories.F2.Ind.strictOppositeFiberNativeCocone_isColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.strictRightStraighteningCocone_isColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.rightStraighteningSmallRecovery
#check @SerrePositivity.InfinityCategories.F2.Ind.rightStraighteningSmallRecovery_projection
#check @SerrePositivity.InfinityCategories.F2.Ind.rightStraighteningSmallRecovery_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Ind.hasKappaFilteredElements_rightStraightening_iff
#check @SerrePositivity.InfinityCategories.F2.Ind.hasKappaFilteredElements_of_strictClassified_colimit
#check @SerrePositivity.InfinityCategories.F2.Ind.isKappaSmall_iSup_subcomplex
#check @SerrePositivity.InfinityCategories.F2.Ind.smallSubcomplexFamily_isCardinalFiltered
#check @SerrePositivity.InfinityCategories.F2.Ind.iSup_smallSubcomplexFamily
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_fresh_vertex_label
#check @SerrePositivity.InfinityCategories.F2.Ind.smallSubcomplexFamilyCocone_isColimit
#check @SerrePositivity.InfinityCategories.F2.Ind.codiscreteProductProjection_isRightCofinal
#check @SerrePositivity.InfinityCategories.F2.Ind.isKappaFiltered_codiscreteProduct_iff
#check @SerrePositivity.InfinityCategories.F2.Ind.codiscreteConeLabelMap_inl
#check @SerrePositivity.InfinityCategories.F2.Ind.codiscreteConeLabelMap_inr
#check @SerrePositivity.InfinityCategories.F2.Ind.codiscreteProductCocone_mono
#check @SerrePositivity.InfinityCategories.F2.Ind.exists_mono_fresh_codiscreteProductCocone
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

#check @SerrePositivity.InfinityCategories.F2.Ind.parametrizedSectionsPre_trivialKanFibration
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionStrictDiagram
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionEvaluate_projection
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionEvaluate_map
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionEvaluate_trivialKanFibration
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionEvaluate_isQCatEquivalence

#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionRightStrictDiagram
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDiagramRightStrict
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDiagramJointEvaluation_value
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDiagramJointValueIso_inv_projection
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDiagramRightValueRecovery_projection
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDiagramRightValueRecovery_isQCatEquivalence

#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionTotalForget
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionScaffold_over_product
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionScaffold_value
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionScaffoldValueMap_eq
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionScaffoldValueMap_trivialKanFibration

#check @SerrePositivity.InfinityCategories.F2.Ind.weightedNerveParameterProjection_leftFibration
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionWeightedProjection_leftFibration
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionTautScaffold_over_product
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionScaffold_isCocartesianScaffold
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionScaffold_isPrecompositionEquivalence
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionTautScaffold_isPrecompositionEquivalence
#check @SerrePositivity.InfinityCategories.F2.Ind.nonempty_underSectionReconstruction
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionReconstruction

#check @SerrePositivity.InfinityCategories.F2.Ind.exists_leftFibrationComparison_of_span
#check @SerrePositivity.InfinityCategories.F2.Ind.underSectionClassificationIso
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDiagramWeightedJointIso
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDiagramWeightedClassificationIso

#check @SerrePositivity.InfinityCategories.F2.Ind.strictLeftFibrationSectionDiagram_map
#check @SerrePositivity.InfinityCategories.F2.Ind.leftFibrationWeightedProjection_leftFibration
#check @SerrePositivity.InfinityCategories.F2.Ind.weightedLeftSectionEvaluation_over_product
#check @SerrePositivity.InfinityCategories.F2.Ind.strictLeftSectionRestriction_comp
#check @SerrePositivity.InfinityCategories.F2.Ind.weightedLeftSectionEvaluation_restriction
#check @SerrePositivity.InfinityCategories.F2.Ind.strictLeftClassificationSectionIso
#check @SerrePositivity.InfinityCategories.F2.Ind.strictLeftFibrationSectionDiagram_coherent

#check @SerrePositivity.InfinityCategories.F2.Ind.strictLeftSectionProductDiagram
#check @SerrePositivity.InfinityCategories.F2.Ind.relativeSection_mixedDiagonal
#check @SerrePositivity.InfinityCategories.F2.Ind.sectionProductReplacementCoefficient_naturality
#check @SerrePositivity.InfinityCategories.F2.Ind.sectionProductWeightedEvaluation_over_product
#check @SerrePositivity.InfinityCategories.F2.Ind.sectionProductScaffold
#check @SerrePositivity.InfinityCategories.F2.Ind.sectionProductScaffold_projection
#check @SerrePositivity.InfinityCategories.F2.Ind.sectionProductScaffold_total

#check @SerrePositivity.InfinityCategories.F2.Ind.weightedParameterGraphIso

#check @SerrePositivity.InfinityCategories.F2.Ind.sectionProductCoefficientFiberIso_total

#check @SerrePositivity.InfinityCategories.F2.Ind.sectionProductValueEvaluation_trivialKanFibration

#check @SerrePositivity.InfinityCategories.F2.Ind.sectionProductScaffold_fiber

#check @SerrePositivity.InfinityCategories.F2.Ind.sectionProductScaffold_isPrecompositionEquivalence

#check @SerrePositivity.InfinityCategories.F2.Ind.sectionProductClassificationIso

#check @SerrePositivity.InfinityCategories.F2.Ind.weightedClassificationRealizationIso

#check @SerrePositivity.InfinityCategories.F2.Ind.sectionProductDiagonalRealization

#check @SerrePositivity.InfinityCategories.F2.Ind.sectionProductJointRealization_eq

#check @SerrePositivity.InfinityCategories.F2.Ind.sectionProductClassificationRealizationIso

#check @SerrePositivity.InfinityCategories.F2.Ind.sectionProductJointRealization_curry

#check @SerrePositivity.InfinityCategories.F2.Ind.strictLeftWeightedClassificationIso

#check @SerrePositivity.InfinityCategories.F2.Ind.leftRightRoundTripDiagram

#check @SerrePositivity.InfinityCategories.F2.Ind.leftRightOppositeDiagramIso

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDiagramRightStrictClassificationIso

#check @SerrePositivity.InfinityCategories.F2.Ind.hasKappaFilteredElements_of_ordinary_colimit

#check @SerrePositivity.InfinityCategories.F2.Ind.isColimitCone_iff_restrict_rightCofinal

#check @SerrePositivity.InfinityCategories.F2.Ind.isRightCofinal_ulift

#check @SerrePositivity.InfinityCategories.F2.Ind.hasKappaFilteredElements_kappaColimitClosed

#check @SerrePositivity.InfinityCategories.F2.Ind.isIndVertex_iff_hasKappaFilteredElements

#check @SerrePositivity.InfinityCategories.F2.Ind.isIndVertex_functorVertex_iff

#check @SerrePositivity.InfinityCategories.F2.Ind.HasSingleFilteredRepresentablePresentation

#check @SerrePositivity.InfinityCategories.F2.Ind.isIndVertex_iff_singleFilteredPresentation

#check @SerrePositivity.InfinityCategories.F2.Ind.PreservesSmallKappaFilteredColimits

#check @SerrePositivity.InfinityCategories.F2.Ind.ind_hasSmallKappaFilteredColimits

#check @SerrePositivity.InfinityCategories.F2.Ind.KappaContinuousFunctorInfinity

#check @SerrePositivity.InfinityCategories.F2.Ind.indKappaContinuousRestriction

#check @SerrePositivity.InfinityCategories.F2.Ind.indDensityCocone_inclusion

#check @SerrePositivity.InfinityCategories.F2.Ind.indVertexDensityCocone_vertex

#check @SerrePositivity.InfinityCategories.F2.Ind.indVertexDensity_image_isColimit

#check @SerrePositivity.InfinityCategories.F2.Ind.continuousHomotopy_vertex_isInvertible

#check @SerrePositivity.InfinityCategories.F2.Ind.indKappaContinuousRestriction_reflects_isInvertibleEdge

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafYonedaSliceFiberMappingIso_projection

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafElementsYonedaSliceMapping_uncurry

#check @SerrePositivity.InfinityCategories.F2.Ind.isQCatEquivalence_of_rightFibration_fibers

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafElementsYonedaSliceValue

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafElementsYonedaSliceComparison_isQCatEquivalence_of_values

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityIdentityValue_factorization

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityIdentityValue_isQCatEquivalence

#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityIdentityReconstruction_projection
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityNativeIdentityValueIso
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityNativeIdentityValue_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Ind.coconeTransformationPointAt_interval
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafElementsYonedaSliceInterval_prism
#check @SerrePositivity.InfinityCategories.F2.Ind.constantIntervalTranspose_vertex
#check @SerrePositivity.InfinityCategories.F2.Ind.densityFiberTransformationRestriction_vertex
#check @SerrePositivity.InfinityCategories.F2.Ind.densityFiberTransformationFamily_native
#check @SerrePositivity.InfinityCategories.F2.Ind.presheafDensityFiberIntervalIso
