import SerrePositivity.InfinityCategories.F2.Presentable.Localization.All
import Lean.Util.CollectAxioms

/-!
P-f の独立監査。新規所有モジュールの全宣言について標準三公理のみを許す。
局所化の存在の完成監査ではなく、現在検証済みの生成族・飽和射圏・小さい compact 候補の監査。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless `SerrePositivity.InfinityCategories.F2.Presentable.Localization |>.isPrefixOf mod do
      continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Presentable localization: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count < 8 then throwError "Presentable localization: expected at least eight declarations"
  logInfo m!"Presentable localization audit passed: {count} declarations, standard axioms only."

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open F2.Presentable F2.Presentable.Localization HomotopyLimits

universe u v

-- 任意の生成添字・任意の元の対象・任意の単体集合パラメータを保持する独立例。
example {X : SSet.{v}} [Quasicategory X] {I : Type u}
    (edges : I → X _⦋1⦌) (z : X _⦋0⦌) (hz : IsLocalObject (Set.range edges) z)
    (i : I) (A : SSet.{v}) :
    Function.Bijective (fun α : ConstantFunctorHom A X (X.δ 0 (edges i)) z ↦
      constantFunctorHomMap A
        (Truncated.HomotopyCategory.homMk (edgeOfSimplex (edges i))) ≫ α) :=
  (isLocalObject_range_iff_constantHom_bijective edges z).mp hz i A

example {C : SSet.{u + 1}} [Quasicategory C] (hC : F2.Presentable.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧
      ∀ i, F2.Compact.IsKappaCompact.{u, u + 1} μ (C.δ 1 (edges i)) ∧
        F2.Compact.IsKappaCompact.{u, u + 1} μ (C.δ 0 (edges i)) :=
  exists_regular_compactEndpoints hC edges σ

#check @isLocalObject_range_iff
#check @isLocalObject_range_iff_constantHom_bijective
#check @localEquivalenceHom_range_iff_constantHom_bijective
#check @localObjects_antitone_of_generators_localEquivalences
#check @localEquivalences_subset_of_generators_localEquivalences
#check @localEquivalences_eq_iff_generators
#check @localEquivalences_eq_iff_localObjects
#check @exists_regular_compactEndpoints
#check @generatedEdges
#check @generatedArrowCategory
#check @generatedArrowInclusion_isFullyFaithful
#check @generatedEdges_smallGeneration
#check @generatedArrow_mem_iff_vertexIso
#check @generatedArrow_colimit_mem
#check @generatedArrow_hasSmallColimits
#check @generatedArrowInclusion_preservesSmallColimits
#check @generatedArrow_isKappaCompact_of_image
#check @compactGeneratedArrows
#check @compactGeneratedArrowVertex
#check @compactGeneratedArrowInclusion_isFullyFaithful
#check @exists_smallCompactGeneratedArrowModel
#check @compactGeneratedArrowInclusion_compact
#check @exists_smallCompactArrowCandidates
#check @generatorArrowVertex_edge
#check @arrow_isPresentable
#check @exists_regular_generatorArrowCardinal
#check @exists_generatorContainingCompactArrowCandidates
#check @exists_generatorContainingIndComparison
#check @generatedSourceCategory
#check @generatedSourceTarget
#check @generatedSourceInclusion_isFullyFaithful
#check @generatedSourceLeg
#check @generatedSourceLeg_mem
#check @sequentialPiece_exists_le
#check @sequentialPiece_isFiltered
#check @sequentialPieceSequence_final
#check @sequentialPiece_hasCardinalLT
#check @compactSource_coslice_factorization
#check @compactInitial_leftFibration_factorization
#check @compactDiagram_cocone_factorization
#check @compactSource_factorization_triangle
#check @generatedArrowInclusion_equivalenceLifting
#check @generatedArrowEvaluation_equivalenceLifting
#check @generatedArrowEvaluation_preservesSmallColimits
#check @generatedSourceCondition_iff_vertexIso
#check @generatedSourceInclusion_equivalenceLifting
#check @generatedSourceTarget_equivalenceLifting
#check @generatedSourceTarget_innerFibration
#check @generatedSource_lift_generatedEdge
#check @generatedSource_terminal_generatedEdge_retraction
#check @generatedSource_terminal_generatedEdge_isSplitMono
#check @initialInclusion_nerve_isRightCofinal
#check @sourceJoinInr_nerve_isRightCofinal
#check @sourceJoinInr_ulift_nerve_isRightCofinal
#check @iteratedSliceUnderIso_sourceRightRestriction
#check @sourceCoslice_isColimitCone_iff_projection
#check @generatedSource_colimit_mem_of_cofinal
#check @generatedSource_nerve_colimit_mem
#check @generatedSource_hasNerveColimit
#check @generatedSource_hasPreservedFiniteColimit
#check @generatedSource_hasFiniteColimits
#check @generatedSourceInclusion_preservesFiniteColimit
#check @generatedSource_finite_colimit_mem
#check @discreteNerve_hasDimensionLT_one
#check @discreteNerve_finite
#check @uliftDiscreteNerve_finite
#check @generatedSource_coproduct_colimit_mem
#check @generatedSource_hasPreservedCoproduct
#check @generatedSource_hasSmallCoproducts
#check @generatedSourceInclusion_preservesSmallCoproducts
#check @generatedSourcePointPullbackEquivalence
#check @generatedSourcePointPullbackEquivalence_fst
#check @generatedSource_hasSmallKappaFilteredColimits
#check @generatedSourceArrows_isKappaAccessibleFunctor
#check @indArrowImageInclusion_equivalenceLifting
#check @indArrowImageEvaluation_equivalenceLifting
#check @indArrowImageEvaluation_isKappaAccessibleFunctor
#check @exists_indArrowImageSource_compactCandidate

#check @indArrowImageFactor_isQCatEquivalence
#check @indArrowImageVertex_mem
#check @indArrowImage_isKappaAccessible
#check @indArrowImage_colimit_mem
#check @indArrowImageInclusion_isFullyFaithful
#check @indArrowImageInclusion_isKappaAccessible
#check @exists_generatorContainingAccessibleIndImage
#check @exists_compactCoveringAccessibleIndImage
#check @sourceCoslice_hasColimit_iff
#check @sourceCoslice_hasSmallColimits

#check @smallDiagramCoslice_hasSmallColimits

#check @compactGeneratedArrow_smallPosetColimit
#check @compactGeneratedArrows_hasSmallPosetColimits
#check @indArrowImage_smallCompactPartialColimit
#check @indArrowImageVertex_hasPresentation
#check @indArrowImageVertex_hasCompactPresentation
#check @exists_ambientCompactIndComparison
#check @exists_regular_refinementArrowCardinal

#check @exists_endpointCompactArrowCardinal
#check @generatedSourceEdge_mem

#check @arrowVertexEdge_source
#check @arrowVertexEdge_target
#check @functorVertexCocone_apex
#check @kanCoconeFamilyAt_diagram
#check @indArrowImage_finitePoset_colimit_mem
#check @indArrowImage_finitePoset_colimit_mem_of_image
#check @indArrowImage_hasFinitePosetColimits
#check @indArrowImageInclusion_preservesFinitePosetColimits
#check @indArrowImage_span_colimit_mem
#check @indArrowImage_hasSpanColimit
#check @indArrowImageInclusion_preservesSpanColimit

#check @exists_operationsCompactArrowCardinal
#check @identityArrow_mem_generatedEdges
#check @indArrowImage_identityArrow
#check @spanRightCollapse_isRightCofinal
#check @spanRightCollapse_left
#check @spanRightCollapse_right
#check @spanRightCollapse_edgeTarget_isColimit
#check @secondProjection_isPushoutSquare
#check @arrowPushoutPrism_zero
#check @arrowPushoutPrism_one
#check @arrowPushoutFamily_isPushout
#check @arrowPushoutFamily_vertex_top
#check @indArrowImage_pushout_bottom_top

#check @invertibleArrow_sourceIdentityIso
#check @indArrowImageEdges
#check @indArrowImageEdges_arrowVertex_iff
#check @indArrowImageEdges_subset_generatedEdges
#check @indArrowImageEdges_mem_of_isInvertible

#check @generatedSourceIdentity_leg_mem
#check @generatedSourceIdentity
#check @generatedSourceIdentity_isInitial

#check @sourceCosliceArrowFamily
#check @sourceCosliceArrowFamily_vertex
#check @sourceCosliceArrowFamily_target
#check @generatedSourceArrows
#check @generatedSourceArrows_inclusion
#check @generatedSourceArrows_target
#check @indArrowImageFamily_hasCommonCompactPresentation

#check @discreteArrowFamilyUncurry
#check @discreteArrowFamily
#check @discreteArrowFamily_evaluate
#check @discreteArrowFamily_precomp
#check @discreteArrowFamilyCocone
#check @discreteArrowFamilyCocone_isColimit
#check @discreteArrowFamilyCocone_apex_evaluate
#check @indArrowImage_smallCoproduct_colimit_mem

#check @indArrowImage_coproduct_colimit_mem_of_compactRows
#check @compactArrowCoproduct_finitePartialDiagram
#check @indArrowImage_compactCoproduct_colimit_mem
#check @indArrowImage_coproduct_colimit_mem
#check @indArrowImage_hasSmallCoproducts
#check @indArrowImageInclusion_preservesSmallCoproducts

#check @sourceArrow_leftVertex
#check @sourceCosliceArrowFamily_source
#check @generatedSourceArrows_source
#check @generatedSourceArrowFiber
#check @generatedSourceToArrowFiber
#check @generatedSourceToArrowFiber_inclusion
#check @sourceCoconeArrowFiberIso
#check @sourceCosliceArrowFiberEquivalence
#check @sourceCoconeArrowFiberIso_inclusion
#check @sourceCosliceArrowFiberEquivalence_inclusion

#check @generatedSourceArrowFiberInclusion
#check @generatedSourceArrowFiberInclusion_ι
#check @generatedSourceFiber_square
#check @generatedSourceFiber_isPullback

#check @sourceArrowFiberCondition
#check @generatedSourceArrowFullFiberIso
#check @generatedSourceArrowFullFiberIso_inclusion
#check @sourceArrowFiberCondition_iff_vertexIso
#check @generatedSourceToArrowFiber_isQCatEquivalence

#check @indArrowImage_hasPreservedFiniteColimit
#check @indArrowImage_hasFiniteColimits
#check @indArrowImageInclusion_preservesFiniteColimit
#check @indArrowImage_finite_colimit_mem

#check @arrowCancellationPrism
#check @arrowCancellationPrism_zero
#check @arrowCancellationPrism_one
#check @arrowCancellationFamily
#check @arrowCancellationFamily_isPushout
#check @arrowCancellationFamily_vertex_first
#check @arrowCancellationFamily_vertex_identity
#check @arrowCancellationFamily_vertex_composite
#check @arrowCancellationFamily_vertex_last
#check @indArrowImage_cancel_left

#check @generatedSource_terminal_pushout_extension
#check @generatedSource_terminal_edge_extension
#check @generatedSource_terminal_precomp_surjective

#check @generatedSource_terminal_mapping_contractible
#check @generatedSource_terminal_coslice_mapping_contractible
#check @generatedSource_isTerminal_iff_coslice_mapping_contractible

#check @indArrowImage_hasPreservedSequentialColimit
#check @generatedSource_hasPreservedSequentialColimit
#check @generatedSource_sequential_colimit_mem

#check @generatedSource_terminal_coslice_isTerminal
#check @generatedSource_terminal_identity_isTerminal
#check @generatedSource_terminal_identity_mapping_contractible

#check @generatedSourceUnderTarget
#check @generatedSourceUnderTarget_identity
#check @generatedSourceUnderTarget_isFullyFaithful
#check @generatedSourceUnderTarget_terminal_mapping_contractible
#check @generatedSourceUnderTarget_lift_generatedEdge
#check @generatedSource_terminal_retractionSpace_contractible

#check @edgeCosliceVertex_generatedSourceLeg
#check @generatedSourceIdentity_isTerminal_of_source_terminal

#check @indArrowImage_hasPreservedSmallColimit
#check @indArrowImage_hasSmallColimits
#check @indArrowImageInclusion_preservesSmallColimits
#check @indArrowImage_isPresentable
#check @indArrowImage_small_colimit_mem
#check @generatedSource_hasPreservedSmallColimit
#check @generatedSource_hasSmallColimits
#check @generatedSourceInclusion_preservesSmallColimits
#check @generatedSource_small_colimit_mem

#check @edgeCosliceUnderIso
#check @edgeCosliceSourceRestriction
#check @edgeCosliceUnderIso_projection
#check @edgeCosliceSourceFiberIso
#check @edgeCosliceSourceFiberIso_hom_ι
#check @edgeCosliceSourceRestriction_projection
#check @edgeCosliceSourceMapping
#check @edgeCosliceSourceMappingFiberIso
#check @edgeCosliceSourceMapping_fibration
#check @edgeCosliceSourceMapping_trivial_of_contractible
#check @isLocalForHom_of_coslice_mapping_contractible

#check @edgeTerminalCocone_vertex
#check @edgeTerminalMappingPoint
#check @edgeTerminalMappingPoint_target_val
#check @edgeTerminalMappingPoint_source_val
#check @pushoutCosliceRestriction_eq
#check @pushoutCosliceRestriction_trivialKanFibration
#check @pushoutCoconeMappingRestriction_trivialKanFibration
#check @squareTopEdge_rightAnodyne
#check @squareTopCosliceRestriction_trivialKanFibration
#check @squareTopCoconeMappingRestriction_trivialKanFibration
#check @pushoutSpanRightMappingRestriction
#check @pushoutSpanRightMappingRestriction_comp
#check @pushoutSpanRightMappingRestriction_fibration
#check @pushoutSpanMappingFiberComparison
#check @pushoutSpanMappingFiberComparison_homotopyEquivalence
#check @squareTopLeft_corner
#check @squareTopSource_eq_leftTarget
#check @squareTopSourceMappingRestriction
#check @squareTopSourceMappingRestriction_comp
#check @squareTopSourceMappingRestriction_fibration
#check @pushoutTopMappingFiberComparison
#check @pushoutTopMappingFiberComparison_homotopyEquivalence
#check @pushoutMappingFiber_contractible_iff
#check @pushoutSpan_rightDiagram
#check @pushoutSpanRightBase
#check @pushoutSpanMapping_isPullback
#check @pushoutSpanSourceFiberIso
#check @pushoutSourceFiber_contractible_iff

#check @edgeTerminalMappingPointAt
#check @edgeTerminalMappingPointAt_target_val
#check @edgeTerminalMappingPointAt_source_val
#check @identityCoconeMappingPoint
#check @generatedSource_terminal_identityMappingFiber_contractible
#check @generatedSource_terminal_normalizedMappingFiber_contractible
#check @generatedSource_terminal_squareTopFiber_contractible
#check @generatedSource_terminal_pushout_sourceFiber_contractible
#check @coconeMappingDiagramChange_val
#check @normalizedCoconeMappingFiberIso
#check @edgeCosliceSourceMapping_contractible_of_raw
#check @exists_compactCoveringPresentableIndImage

#check @pushoutSpanRightBase_val
#check @pushoutSpanRightBase_terminal_val
#check @squareLeftEdge_target_of_edge
#check @pushoutSpanRightBase_terminal_of_edgeFiber
#check @generatedSource_terminal_edgeMappingFiber_contractible
#check @generatedSource_terminal_edge_isLocalForHom
#check @generatedSource_terminal_target_isLocalObject_generated
#check @generatedSource_terminal_target_isLocalObject
#check @generatedSource_isTerminal_of_target_isLocalObject
#check @generatedSource_isTerminal_iff_target_isLocalObject
#check @generatedSource_isPresentable_of_isAccessible
#check @exists_generatedSource_terminal_of_isAccessible
#check @exists_generatedSource_localReplacement_of_isAccessible
#check @exists_operationsPresentableIndImage
#check @exists_compactCoveringOperationsPresentableIndImage
#check @indArrowImageVertex_of_retract
#check @generatedSource_isKappaAccessible_iff_pointPullback
#check @generatedSource_isAccessible_iff_pointPullback
#check @exists_generatedSource_localReplacement_of_accessiblePointPullback
#check @triangle_isPresentable
#check @triangleFace_preservesSmallColimits
#check @exists_triangleFacesCompactCardinal
#check @HasCompactTrianglePosetPresentation
#check @triangle_hasCompactPosetPresentation
#check @exists_compactTrianglePosetPresentations
#check @indArrowImageEdges_mem_of_compact_generated
#check @indArrowImageEdges_comp_of_compact
#check @indArrowImageEdges_cancel_left_of_compact
#check @indArrowImageEdges_cancel_right_of_compact
#check @indArrowImage_ambientFiltered_colimit_mem
#check @indArrowImage_triangleFace_colimit_mem
#check @exists_triangleOperationsCompactCardinal
#check @exists_triangleOperationsPresentableIndImage
#check @triangleFace_vertex
#check @indArrowImage_triangle_missing_of_compact
#check @indArrowImage_triangle_missing_of_refinedPresentation
#check @compactCocone_factorization_relative_terminalPrefix
#check @compactDiagram_factorization_relative_terminalPrefix
#check @terminalPrefix_cosliceProjection_isRightCofinal
#check @terminalPrefix_restrictedCocone_isColimit
#check @compactDiagram_factorization_over_terminalPrefixPresentation
#check @sequentialCoconeExtension
#check @sequentialCoconeExtension_target
#check @sequentialCoconeExtension_restrict_val
#check @sequentialCoconeExtension_vertex
#check @sequentialCoconeExtension_comparison_edge
#check @sequentialCoconeExtension_leg
#check @sequentialCoconeExtension_val
#check @sequentialCoconeExtension_restrict_naturality

example {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s) :
    IsLocalObject (Set.range edges) ((generatedSourceTarget edges x).app _ s) :=
  generatedSource_terminal_target_isLocalObject hC edges x s hs

#check @CompactPresentationComparison
#check @CompactPresentationComparison.swap
#check @CompactPresentationComparison.swap_swap
#check @CompactPresentationComparison.vertex_left
#check @CompactPresentationComparison.vertex_right
#check @comparisonLeftStages
#check @comparisonLeftCocone
#check @ComparisonLeftFactor
#check @nonempty_comparisonLeftFactor
#check @comparisonLeftStages_projection
#check @ComparisonLeftFactor.vertex
#check @ComparisonLeftFactor.compact

#check @coconeTransportLeg_restrict_edge
#check @compactSource_factorization_after_point
#check @exists_sequentialSeed_bound
#check @compactPresentations_initialTriangle
