import SerrePositivity.KST.Comparison
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# K-L2 比較定理の公理監査

概要：現在公開する全宣言の型と推移的な依存公理を確認する。
方針：#check @ と #print axioms を併用する。
規約：許可する公理は propext、Classical.choice、Quot.sound のみ。
使われ方：SS03 (2.9) と KST 式 (2.2) の保存単位。比較定理全体は未完了。
-/

set_option pp.universes true
set_option pp.explicit true










/- 自動生成された公開補題・射影も含め、名前空間全体を許可リストで検査する。 -/
run_cmd do
  let env ← Lean.getEnv
  let nsPrefix := `SerrePositivity.KST.Comparison
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if nsPrefix.isPrefixOf name then
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          throwError "K-L2: {name} depends on forbidden axiom {ax}"
      count := count + 1
  Lean.logInfo m!"K-L2 namespace audit: {count} declarations; standard three axioms only"






















































































-- ActionBarCoordinates.lean

#check @SerrePositivity.KST.Comparison.monoidPrefixLabel
#print axioms SerrePositivity.KST.Comparison.monoidPrefixLabel

#check @SerrePositivity.KST.Comparison.monoidPrefixLabel_zero
#print axioms SerrePositivity.KST.Comparison.monoidPrefixLabel_zero

#check @SerrePositivity.KST.Comparison.monoidPrefixLabel_map
#print axioms SerrePositivity.KST.Comparison.monoidPrefixLabel_map

#check @SerrePositivity.KST.Comparison.regularActionLift
#print axioms SerrePositivity.KST.Comparison.regularActionLift

#check @SerrePositivity.KST.Comparison.regularActionLift_initial
#print axioms SerrePositivity.KST.Comparison.regularActionLift_initial

#check @SerrePositivity.KST.Comparison.regularActionLift_projection
#print axioms SerrePositivity.KST.Comparison.regularActionLift_projection

#check @SerrePositivity.KST.Comparison.regularActionLift_reconstruct
#print axioms SerrePositivity.KST.Comparison.regularActionLift_reconstruct

#check @SerrePositivity.KST.Comparison.regularActionCoordinateEquiv
#print axioms SerrePositivity.KST.Comparison.regularActionCoordinateEquiv

#check @SerrePositivity.KST.Comparison.regularBarRowIso
#print axioms SerrePositivity.KST.Comparison.regularBarRowIso

#check @SerrePositivity.KST.Comparison.regularActionCoordinate_whisker
#print axioms SerrePositivity.KST.Comparison.regularActionCoordinate_whisker


-- ActionBarSquares.lean

#check @SerrePositivity.KST.Comparison.actionBarBase
#print axioms SerrePositivity.KST.Comparison.actionBarBase

#check @SerrePositivity.KST.Comparison.actionBarTotal
#print axioms SerrePositivity.KST.Comparison.actionBarTotal

#check @SerrePositivity.KST.Comparison.actionBarProjection
#print axioms SerrePositivity.KST.Comparison.actionBarProjection

#check @SerrePositivity.KST.Comparison.regularBarRowIso_fst
#print axioms SerrePositivity.KST.Comparison.regularBarRowIso_fst

#check @SerrePositivity.KST.Comparison.actionBarPrefix
#print axioms SerrePositivity.KST.Comparison.actionBarPrefix

#check @SerrePositivity.KST.Comparison.actionBarCoordinate_naturality
#print axioms SerrePositivity.KST.Comparison.actionBarCoordinate_naturality

#check @SerrePositivity.KST.Comparison.actionBarSquare
#print axioms SerrePositivity.KST.Comparison.actionBarSquare

#check @SerrePositivity.KST.Comparison.actionBarSquare_isHomotopyPullback
#print axioms SerrePositivity.KST.Comparison.actionBarSquare_isHomotopyPullback


-- ActualSequentialComparison.lean

#check @SerrePositivity.KST.Comparison.colimitCoconeIso_naturality
#print axioms SerrePositivity.KST.Comparison.colimitCoconeIso_naturality

#check @SerrePositivity.KST.Comparison.actual_sequential_homotopyPullback
#print axioms SerrePositivity.KST.Comparison.actual_sequential_homotopyPullback


-- AlternativeFiberCriterion.lean

#check @SerrePositivity.KST.Comparison.isHomotopyPullback_iff_alternative_fiber
#print axioms SerrePositivity.KST.Comparison.isHomotopyPullback_iff_alternative_fiber


-- AlternativePullback.lean

#check @SerrePositivity.KST.Comparison.alternativePullbackComparison
#print axioms SerrePositivity.KST.Comparison.alternativePullbackComparison

#check @SerrePositivity.KST.Comparison.alternativePullbackComparison_fst
#print axioms SerrePositivity.KST.Comparison.alternativePullbackComparison_fst

#check @SerrePositivity.KST.Comparison.alternativePullbackComparison_snd
#print axioms SerrePositivity.KST.Comparison.alternativePullbackComparison_snd

#check @SerrePositivity.KST.Comparison.isHomotopyPullback_iff_alternative
#print axioms SerrePositivity.KST.Comparison.isHomotopyPullback_iff_alternative


-- ArbitraryBasePullback.lean

#check @SerrePositivity.KST.Comparison.pullback_localized_isIso
#print axioms SerrePositivity.KST.Comparison.pullback_localized_isIso

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_localized_isIso_anyBase
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_localized_isIso_anyBase


-- BarEdge.lean

#check @SerrePositivity.KST.Comparison.monoidEdgeSimplex
#print axioms SerrePositivity.KST.Comparison.monoidEdgeSimplex

#check @SerrePositivity.KST.Comparison.monoidEdgeSimplex_map
#print axioms SerrePositivity.KST.Comparison.monoidEdgeSimplex_map

#check @SerrePositivity.KST.Comparison.monoidBarEdgeAt
#print axioms SerrePositivity.KST.Comparison.monoidBarEdgeAt

#check @SerrePositivity.KST.Comparison.monoidBarEdgeMap
#print axioms SerrePositivity.KST.Comparison.monoidBarEdgeMap

#check @SerrePositivity.KST.Comparison.monoidBarEdgeAt_const
#print axioms SerrePositivity.KST.Comparison.monoidBarEdgeAt_const

#check @SerrePositivity.KST.Comparison.monoidBarEdgeMap_zero
#print axioms SerrePositivity.KST.Comparison.monoidBarEdgeMap_zero

#check @SerrePositivity.KST.Comparison.monoidBarEdgeMap_one
#print axioms SerrePositivity.KST.Comparison.monoidBarEdgeMap_one

#check @SerrePositivity.KST.Comparison.monoidBarLoopFamily
#print axioms SerrePositivity.KST.Comparison.monoidBarLoopFamily


-- BarFundamentalComparison.lean

#check @SerrePositivity.KST.Comparison.monoidBarFundamentalEquiv
#print axioms SerrePositivity.KST.Comparison.monoidBarFundamentalEquiv

#check @SerrePositivity.KST.Comparison.stableHatGLBarFundamentalEquiv
#print axioms SerrePositivity.KST.Comparison.stableHatGLBarFundamentalEquiv


-- BarFundamentalMultiplication.lean

#check @SerrePositivity.KST.Comparison.monoidBarFundamentalClass
#print axioms SerrePositivity.KST.Comparison.monoidBarFundamentalClass

#check @SerrePositivity.KST.Comparison.monoidBarFundamentalClass_mk
#print axioms SerrePositivity.KST.Comparison.monoidBarFundamentalClass_mk

#check @SerrePositivity.KST.Comparison.monoidBarFundamentalClass_bijective
#print axioms SerrePositivity.KST.Comparison.monoidBarFundamentalClass_bijective

#check @SerrePositivity.KST.Comparison.monoidBarFundamentalClass_mul
#print axioms SerrePositivity.KST.Comparison.monoidBarFundamentalClass_mul

#check @SerrePositivity.KST.Comparison.monoidBarFundamentalMulEquiv
#print axioms SerrePositivity.KST.Comparison.monoidBarFundamentalMulEquiv

#check @SerrePositivity.KST.Comparison.stableHatGLBarFundamentalMulEquiv
#print axioms SerrePositivity.KST.Comparison.stableHatGLBarFundamentalMulEquiv


-- BarFundamentalRepresentatives.lean

#check @SerrePositivity.KST.Comparison.monoidVertexNerveKanMap
#print axioms SerrePositivity.KST.Comparison.monoidVertexNerveKanMap

#check @SerrePositivity.KST.Comparison.monoidVertexNerveKanMap_point
#print axioms SerrePositivity.KST.Comparison.monoidVertexNerveKanMap_point

#check @SerrePositivity.KST.Comparison.monoidBarVertexLoop
#print axioms SerrePositivity.KST.Comparison.monoidBarVertexLoop

#check @SerrePositivity.KST.Comparison.groupCompletionVertex_eq_barLoop
#print axioms SerrePositivity.KST.Comparison.groupCompletionVertex_eq_barLoop


-- BarLocalizedEquivalence.lean

#check @SerrePositivity.KST.Comparison.monoidBarRowsMap
#print axioms SerrePositivity.KST.Comparison.monoidBarRowsMap

#check @SerrePositivity.KST.Comparison.monoidBarRowIso_naturality
#print axioms SerrePositivity.KST.Comparison.monoidBarRowIso_naturality

#check @SerrePositivity.KST.Comparison.monoidBarRowsMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.monoidBarRowsMap_localized_isIso

#check @SerrePositivity.KST.Comparison.monoidBarDiagonalFlipIso
#print axioms SerrePositivity.KST.Comparison.monoidBarDiagonalFlipIso

#check @SerrePositivity.KST.Comparison.monoidBarDiagonalFlipIso_naturality
#print axioms SerrePositivity.KST.Comparison.monoidBarDiagonalFlipIso_naturality

#check @SerrePositivity.KST.Comparison.monoidBarMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.monoidBarMap_localized_isIso


-- BarPositiveDelooping.lean

#check @SerrePositivity.KST.Comparison.monoidGroupCompletionPointedMap
#print axioms SerrePositivity.KST.Comparison.monoidGroupCompletionPointedMap

#check @SerrePositivity.KST.Comparison.pointedKanPositiveHomotopyMulEquiv
#print axioms SerrePositivity.KST.Comparison.pointedKanPositiveHomotopyMulEquiv

#check @SerrePositivity.KST.Comparison.monoidBarPositiveHomotopyMulEquiv
#print axioms SerrePositivity.KST.Comparison.monoidBarPositiveHomotopyMulEquiv

#check @SerrePositivity.KST.Comparison.stableHatGLBarPositiveHomotopyMulEquiv
#print axioms SerrePositivity.KST.Comparison.stableHatGLBarPositiveHomotopyMulEquiv


-- BarSegal.lean

#check @SerrePositivity.KST.Comparison.monoidSingleObj_eqToHom
#print axioms SerrePositivity.KST.Comparison.monoidSingleObj_eqToHom

#check @SerrePositivity.KST.Comparison.monoidWordSimplex
#print axioms SerrePositivity.KST.Comparison.monoidWordSimplex

#check @SerrePositivity.KST.Comparison.monoidWordLabels
#print axioms SerrePositivity.KST.Comparison.monoidWordLabels

#check @SerrePositivity.KST.Comparison.monoidWordLabels_simplex
#print axioms SerrePositivity.KST.Comparison.monoidWordLabels_simplex

#check @SerrePositivity.KST.Comparison.monoidWordSimplex_labels
#print axioms SerrePositivity.KST.Comparison.monoidWordSimplex_labels

#check @SerrePositivity.KST.Comparison.monoidWordEquiv
#print axioms SerrePositivity.KST.Comparison.monoidWordEquiv

#check @SerrePositivity.KST.Comparison.monoidWordLabels_map
#print axioms SerrePositivity.KST.Comparison.monoidWordLabels_map

#check @SerrePositivity.KST.Comparison.monoidTupleSpace
#print axioms SerrePositivity.KST.Comparison.monoidTupleSpace

#check @SerrePositivity.KST.Comparison.monoidBarRowIso
#print axioms SerrePositivity.KST.Comparison.monoidBarRowIso


-- BarTupleKan.lean

#check @SerrePositivity.KST.Comparison.monoidTupleProjection
#print axioms SerrePositivity.KST.Comparison.monoidTupleProjection

#check @SerrePositivity.KST.Comparison.monoidTupleLift
#print axioms SerrePositivity.KST.Comparison.monoidTupleLift

#check @SerrePositivity.KST.Comparison.monoidTupleSpace_kanComplex
#print axioms SerrePositivity.KST.Comparison.monoidTupleSpace_kanComplex


-- BarTupleMaps.lean

#check @SerrePositivity.KST.Comparison.monoidTupleMap
#print axioms SerrePositivity.KST.Comparison.monoidTupleMap

#check @SerrePositivity.KST.Comparison.monoidTupleSuccIso
#print axioms SerrePositivity.KST.Comparison.monoidTupleSuccIso

#check @SerrePositivity.KST.Comparison.monoidTupleSuccIso_naturality
#print axioms SerrePositivity.KST.Comparison.monoidTupleSuccIso_naturality

#check @SerrePositivity.KST.Comparison.monoidTupleMap_zero_isIso
#print axioms SerrePositivity.KST.Comparison.monoidTupleMap_zero_isIso

#check @SerrePositivity.KST.Comparison.monoidTupleMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.monoidTupleMap_localized_isIso


-- BarVertexInclusion.lean

#check @SerrePositivity.KST.Comparison.monoidVertexInclusion
#print axioms SerrePositivity.KST.Comparison.monoidVertexInclusion

#check @SerrePositivity.KST.Comparison.constantMonoidBarIso
#print axioms SerrePositivity.KST.Comparison.constantMonoidBarIso

#check @SerrePositivity.KST.Comparison.monoidVertexNerveMap
#print axioms SerrePositivity.KST.Comparison.monoidVertexNerveMap

#check @SerrePositivity.KST.Comparison.monoidVertexNerveMap_point
#print axioms SerrePositivity.KST.Comparison.monoidVertexNerveMap_point

#check @SerrePositivity.KST.Comparison.monoidVertexNerveMap_edge
#print axioms SerrePositivity.KST.Comparison.monoidVertexNerveMap_edge


-- BarZeroEvaluation.lean

#check @SerrePositivity.KST.Comparison.regularBarZeroRow_evaluation
#print axioms SerrePositivity.KST.Comparison.regularBarZeroRow_evaluation

#check @SerrePositivity.KST.Comparison.monoidBarZeroRow_evaluation
#print axioms SerrePositivity.KST.Comparison.monoidBarZeroRow_evaluation


-- BarZeroRows.lean

#check @SerrePositivity.KST.Comparison.regularBarZeroRowIso
#print axioms SerrePositivity.KST.Comparison.regularBarZeroRowIso

#check @SerrePositivity.KST.Comparison.monoidBarZeroRowMap
#print axioms SerrePositivity.KST.Comparison.monoidBarZeroRowMap

#check @SerrePositivity.KST.Comparison.monoidBarZeroRowIsTerminal
#print axioms SerrePositivity.KST.Comparison.monoidBarZeroRowIsTerminal

#check @SerrePositivity.KST.Comparison.monoidBarZeroRowIso
#print axioms SerrePositivity.KST.Comparison.monoidBarZeroRowIso


-- BasedPathEndpoint.lean

#check @SerrePositivity.KST.Comparison.basedPathEndpoint_evaluation
#print axioms SerrePositivity.KST.Comparison.basedPathEndpoint_evaluation

#check @SerrePositivity.KST.Comparison.basedPathFamilyMap_endpoint
#print axioms SerrePositivity.KST.Comparison.basedPathFamilyMap_endpoint


-- BasedPathFamily.lean

#check @SerrePositivity.KST.Comparison.basedPathFamily_basepoint
#print axioms SerrePositivity.KST.Comparison.basedPathFamily_basepoint

#check @SerrePositivity.KST.Comparison.basedPathFamilyMap
#print axioms SerrePositivity.KST.Comparison.basedPathFamilyMap

#check @SerrePositivity.KST.Comparison.basedPathFamilyMap_ι
#print axioms SerrePositivity.KST.Comparison.basedPathFamilyMap_ι


-- BoundaryFaceRepresentation.lean

#check @SerrePositivity.KST.Comparison.vertexFace_le_boundary
#print axioms SerrePositivity.KST.Comparison.vertexFace_le_boundary

#check @SerrePositivity.KST.Comparison.vertexFaceEmbedding
#print axioms SerrePositivity.KST.Comparison.vertexFaceEmbedding

#check @SerrePositivity.KST.Comparison.vertexFaceEmbedding_mono
#print axioms SerrePositivity.KST.Comparison.vertexFaceEmbedding_mono

#check @SerrePositivity.KST.Comparison.boundaryVertexFaceIso
#print axioms SerrePositivity.KST.Comparison.boundaryVertexFaceIso

#check @SerrePositivity.KST.Comparison.boundaryVertexFaceIso_hom_ι
#print axioms SerrePositivity.KST.Comparison.boundaryVertexFaceIso_hom_ι

#check @SerrePositivity.KST.Comparison.boundaryVertexFace_representation
#print axioms SerrePositivity.KST.Comparison.boundaryVertexFace_representation


-- BoundaryVertexFaces.lean

#check @SerrePositivity.KST.Comparison.boundaryVertexFace
#print axioms SerrePositivity.KST.Comparison.boundaryVertexFace

#check @SerrePositivity.KST.Comparison.boundaryVertexFace_inf
#print axioms SerrePositivity.KST.Comparison.boundaryVertexFace_inf

#check @SerrePositivity.KST.Comparison.boundaryVertexFace_univ
#print axioms SerrePositivity.KST.Comparison.boundaryVertexFace_univ

#check @SerrePositivity.KST.Comparison.boundaryVertexFace_empty
#print axioms SerrePositivity.KST.Comparison.boundaryVertexFace_empty

#check @SerrePositivity.KST.Comparison.boundaryVertexFace_finset_inf
#print axioms SerrePositivity.KST.Comparison.boundaryVertexFace_finset_inf

#check @SerrePositivity.KST.Comparison.boundaryVertexFace_coface_cover
#print axioms SerrePositivity.KST.Comparison.boundaryVertexFace_coface_cover

#check @SerrePositivity.KST.Comparison.cofaceVertexIntersection_ne_univ
#print axioms SerrePositivity.KST.Comparison.cofaceVertexIntersection_ne_univ


-- CartesianTensorSquare.lean

#check @SerrePositivity.KST.Comparison.cartesianTensorSquare_isPullback
#print axioms SerrePositivity.KST.Comparison.cartesianTensorSquare_isPullback


-- ChainPairContraction.lean

#check @SerrePositivity.KST.Comparison.intervalMapSimplicialHomotopy
#print axioms SerrePositivity.KST.Comparison.intervalMapSimplicialHomotopy

#check @SerrePositivity.KST.Comparison.chainHomotopyEquivOfPairContraction
#print axioms SerrePositivity.KST.Comparison.chainHomotopyEquivOfPairContraction

#check @SerrePositivity.KST.Comparison.constantCoefficientChainHomotopyEquivOfPairContraction
#print axioms SerrePositivity.KST.Comparison.constantCoefficientChainHomotopyEquivOfPairContraction

#check @SerrePositivity.KST.Comparison.constantCoefficientHornChainHomotopyEquiv
#print axioms SerrePositivity.KST.Comparison.constantCoefficientHornChainHomotopyEquiv

#check @SerrePositivity.KST.Comparison.constantCoefficientHorn_quasiIso
#print axioms SerrePositivity.KST.Comparison.constantCoefficientHorn_quasiIso


-- CoconeBaseComparison.lean

#check @SerrePositivity.KST.Comparison.coconeBaseSquare
#print axioms SerrePositivity.KST.Comparison.coconeBaseSquare

#check @SerrePositivity.KST.Comparison.coconeBaseFiberComparison
#print axioms SerrePositivity.KST.Comparison.coconeBaseFiberComparison

#check @SerrePositivity.KST.Comparison.coconeBaseFiberComparison_cocone
#print axioms SerrePositivity.KST.Comparison.coconeBaseFiberComparison_cocone


-- CoconeBaseGluing.lean

#check @SerrePositivity.KST.Comparison.coconeBase_homotopyPullback_of_span
#print axioms SerrePositivity.KST.Comparison.coconeBase_homotopyPullback_of_span


-- CoconeOverBase.lean

#check @SerrePositivity.KST.Comparison.coconeOverDiagram
#print axioms SerrePositivity.KST.Comparison.coconeOverDiagram

#check @SerrePositivity.KST.Comparison.coconeOverCocone
#print axioms SerrePositivity.KST.Comparison.coconeOverCocone

#check @SerrePositivity.KST.Comparison.coconeOverCoconeIsColimit
#print axioms SerrePositivity.KST.Comparison.coconeOverCoconeIsColimit

#check @SerrePositivity.KST.Comparison.fiberCocone
#print axioms SerrePositivity.KST.Comparison.fiberCocone

#check @SerrePositivity.KST.Comparison.fiberCoconeIsColimit
#print axioms SerrePositivity.KST.Comparison.fiberCoconeIsColimit

#check @SerrePositivity.KST.Comparison.fiberCocone_ι_fst
#print axioms SerrePositivity.KST.Comparison.fiberCocone_ι_fst

#check @SerrePositivity.KST.Comparison.fiberCocone_ι_snd
#print axioms SerrePositivity.KST.Comparison.fiberCocone_ι_snd


-- CoefficientMatrixStabilization.lean

#check @SerrePositivity.KST.Comparison.coefficientMatrixStabilization
#print axioms SerrePositivity.KST.Comparison.coefficientMatrixStabilization

#check @SerrePositivity.KST.Comparison.coefficientMatrixStabilization_apply_sum
#print axioms SerrePositivity.KST.Comparison.coefficientMatrixStabilization_apply_sum

#check @SerrePositivity.KST.Comparison.coefficientMatrixRankSequence
#print axioms SerrePositivity.KST.Comparison.coefficientMatrixRankSequence

#check @SerrePositivity.KST.Comparison.grpCat_hasSequentialColimits
#print axioms SerrePositivity.KST.Comparison.grpCat_hasSequentialColimits

#check @SerrePositivity.KST.Comparison.stableCoefficientMatrices
#print axioms SerrePositivity.KST.Comparison.stableCoefficientMatrices


-- CommonTrivialRefinement.lean

#check @SerrePositivity.KST.Comparison.commonTrivialFibrationRefinement
#print axioms SerrePositivity.KST.Comparison.commonTrivialFibrationRefinement


-- ComponentHomotopy.lean

#check @SerrePositivity.KST.Comparison.componentRelStructLift
#print axioms SerrePositivity.KST.Comparison.componentRelStructLift

#check @SerrePositivity.KST.Comparison.componentHomotopyMap_bijective
#print axioms SerrePositivity.KST.Comparison.componentHomotopyMap_bijective

#check @SerrePositivity.KST.Comparison.componentPositiveHomotopyMulEquiv
#print axioms SerrePositivity.KST.Comparison.componentPositiveHomotopyMulEquiv


-- ComponentKan.lean

#check @SerrePositivity.KST.Comparison.componentSimplexLift
#print axioms SerrePositivity.KST.Comparison.componentSimplexLift

#check @SerrePositivity.KST.Comparison.componentSimplexLift_ι
#print axioms SerrePositivity.KST.Comparison.componentSimplexLift_ι

#check @SerrePositivity.KST.Comparison.simplex_in_component_of_face
#print axioms SerrePositivity.KST.Comparison.simplex_in_component_of_face

#check @SerrePositivity.KST.Comparison.componentSubcomplex_kanComplex
#print axioms SerrePositivity.KST.Comparison.componentSubcomplex_kanComplex


-- ComponentPointedSimplex.lean

#check @SerrePositivity.KST.Comparison.simplexClass_yoneda_const
#print axioms SerrePositivity.KST.Comparison.simplexClass_yoneda_const

#check @SerrePositivity.KST.Comparison.pointedSimplex_class
#print axioms SerrePositivity.KST.Comparison.pointedSimplex_class

#check @SerrePositivity.KST.Comparison.componentPtSimplexLift
#print axioms SerrePositivity.KST.Comparison.componentPtSimplexLift

#check @SerrePositivity.KST.Comparison.componentPtSimplexLift_map
#print axioms SerrePositivity.KST.Comparison.componentPtSimplexLift_map


-- ComponentSubcomplex.lean

#check @SerrePositivity.KST.Comparison.componentSubcomplex
#print axioms SerrePositivity.KST.Comparison.componentSubcomplex

#check @SerrePositivity.KST.Comparison.componentVertex
#print axioms SerrePositivity.KST.Comparison.componentVertex

#check @SerrePositivity.KST.Comparison.componentEdge
#print axioms SerrePositivity.KST.Comparison.componentEdge

#check @SerrePositivity.KST.Comparison.componentVertex_sound
#print axioms SerrePositivity.KST.Comparison.componentVertex_sound

#check @SerrePositivity.KST.Comparison.componentClassMap
#print axioms SerrePositivity.KST.Comparison.componentClassMap

#check @SerrePositivity.KST.Comparison.componentClassEquiv
#print axioms SerrePositivity.KST.Comparison.componentClassEquiv


-- ConnectiveTruncation.lean

#check @SerrePositivity.KST.Comparison.supported_nonpositive_of_connective
#print axioms SerrePositivity.KST.Comparison.supported_nonpositive_of_connective

#check @SerrePositivity.KST.Comparison.quasiIso_connective_truncation
#print axioms SerrePositivity.KST.Comparison.quasiIso_connective_truncation

#check @SerrePositivity.KST.Comparison.DGAlgebraModel.quasiIso_truncation
#print axioms SerrePositivity.KST.Comparison.DGAlgebraModel.quasiIso_truncation


-- ConstantCoefficientComparison.lean

#check @SerrePositivity.KST.Comparison.constantCoefficientSimplicialFunctor
#print axioms SerrePositivity.KST.Comparison.constantCoefficientSimplicialFunctor

#check @SerrePositivity.KST.Comparison.constantCoefficientUnit
#print axioms SerrePositivity.KST.Comparison.constantCoefficientUnit

#check @SerrePositivity.KST.Comparison.constantCoefficientComparison
#print axioms SerrePositivity.KST.Comparison.constantCoefficientComparison

#check @SerrePositivity.KST.Comparison.constantCoefficientComparison_unit
#print axioms SerrePositivity.KST.Comparison.constantCoefficientComparison_unit

#check @SerrePositivity.KST.Comparison.constantCoefficientComparison_app
#print axioms SerrePositivity.KST.Comparison.constantCoefficientComparison_app

#check @SerrePositivity.KST.Comparison.constantCoefficientSimplicialIso
#print axioms SerrePositivity.KST.Comparison.constantCoefficientSimplicialIso


-- ConstantCoefficientMaps.lean

#check @SerrePositivity.KST.Comparison.constantCoefficientComparison_naturality
#print axioms SerrePositivity.KST.Comparison.constantCoefficientComparison_naturality

#check @SerrePositivity.KST.Comparison.constantLocalCoefficientChainsIso
#print axioms SerrePositivity.KST.Comparison.constantLocalCoefficientChainsIso

#check @SerrePositivity.KST.Comparison.constantLocalCoefficientChainsIso_naturality
#print axioms SerrePositivity.KST.Comparison.constantLocalCoefficientChainsIso_naturality

#check @SerrePositivity.KST.Comparison.normalizedMooreMap_quasiIso_iff
#print axioms SerrePositivity.KST.Comparison.normalizedMooreMap_quasiIso_iff

#check @SerrePositivity.KST.Comparison.localConstantCoefficientMap_quasiIso_iff
#print axioms SerrePositivity.KST.Comparison.localConstantCoefficientMap_quasiIso_iff


-- ContractibleComparison.lean

#check @SerrePositivity.KST.Comparison.contractedSpace_terminal_localized_isIso
#print axioms SerrePositivity.KST.Comparison.contractedSpace_terminal_localized_isIso

#check @SerrePositivity.KST.Comparison.map_between_contractible_localized_isIso
#print axioms SerrePositivity.KST.Comparison.map_between_contractible_localized_isIso


-- CoproductPullbacks.lean

#check @SerrePositivity.KST.Comparison.coproductInclusions_isPullback
#print axioms SerrePositivity.KST.Comparison.coproductInclusions_isPullback

#check @SerrePositivity.KST.Comparison.binaryCoproductPullback
#print axioms SerrePositivity.KST.Comparison.binaryCoproductPullback

#check @SerrePositivity.KST.Comparison.coproductSquare_isPullback
#print axioms SerrePositivity.KST.Comparison.coproductSquare_isPullback


-- CutDegeneracy.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCutDegeneracy_singleton
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCutDegeneracy_singleton

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_le_castSucc_iff
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_le_castSucc_iff

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_le_succ_iff
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_le_succ_iff


-- CylinderBoundary.lean

#check @SerrePositivity.KST.Comparison.simplexZeroTensorIso
#print axioms SerrePositivity.KST.Comparison.simplexZeroTensorIso

#check @SerrePositivity.KST.Comparison.cylinderBoundaryIso
#print axioms SerrePositivity.KST.Comparison.cylinderBoundaryIso

#check @SerrePositivity.KST.Comparison.cylinderBoundaryIso_inl
#print axioms SerrePositivity.KST.Comparison.cylinderBoundaryIso_inl

#check @SerrePositivity.KST.Comparison.cylinderBoundaryIso_inr
#print axioms SerrePositivity.KST.Comparison.cylinderBoundaryIso_inr

#check @SerrePositivity.KST.Comparison.simplexZeroTensorIso_zero
#print axioms SerrePositivity.KST.Comparison.simplexZeroTensorIso_zero

#check @SerrePositivity.KST.Comparison.simplexZeroTensorIso_one
#print axioms SerrePositivity.KST.Comparison.simplexZeroTensorIso_one

#check @SerrePositivity.KST.Comparison.cylinderEndpoints_factor
#print axioms SerrePositivity.KST.Comparison.cylinderEndpoints_factor

#check @SerrePositivity.KST.Comparison.cylinderEndpoints_mono
#print axioms SerrePositivity.KST.Comparison.cylinderEndpoints_mono


-- CylinderBoundaryPullback.lean

#check @SerrePositivity.KST.Comparison.simplexZeroTensorIso_inv_naturality
#print axioms SerrePositivity.KST.Comparison.simplexZeroTensorIso_inv_naturality

#check @SerrePositivity.KST.Comparison.cylinderBoundaryIso_naturality
#print axioms SerrePositivity.KST.Comparison.cylinderBoundaryIso_naturality

#check @SerrePositivity.KST.Comparison.cylinderEndpoints_isPullback
#print axioms SerrePositivity.KST.Comparison.cylinderEndpoints_isPullback


-- DGAlgebra.lean

#check @SerrePositivity.KST.Comparison.DGAlgebraModel
#print axioms SerrePositivity.KST.Comparison.DGAlgebraModel

#check @SerrePositivity.KST.Comparison.DGAlgebraModel.IsConnective
#print axioms SerrePositivity.KST.Comparison.DGAlgebraModel.IsConnective

#check @SerrePositivity.KST.Comparison.dgAlgebraGamma
#print axioms SerrePositivity.KST.Comparison.dgAlgebraGamma

#check @SerrePositivity.KST.Comparison.dgAlgebraComponents
#print axioms SerrePositivity.KST.Comparison.dgAlgebraComponents

#check @SerrePositivity.KST.Comparison.dgAlgebraHatGL
#print axioms SerrePositivity.KST.Comparison.dgAlgebraHatGL

#check @SerrePositivity.KST.Comparison.dgAlgebraHatGLGroup
#print axioms SerrePositivity.KST.Comparison.dgAlgebraHatGLGroup

#check @SerrePositivity.KST.Comparison.dgAlgebraHatGLComponents
#print axioms SerrePositivity.KST.Comparison.dgAlgebraHatGLComponents


-- DegeneracyFibers.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_val
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_val

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_next_fiber
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_next_fiber

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_self_fiber
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_self_fiber

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_castSucc
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_castSucc


-- DiagonalRowDesc.lean

#check @SerrePositivity.KST.Comparison.diagonalRowDesc
#print axioms SerrePositivity.KST.Comparison.diagonalRowDesc

#check @SerrePositivity.KST.Comparison.diagonalRowEvaluation_desc
#print axioms SerrePositivity.KST.Comparison.diagonalRowEvaluation_desc

#check @SerrePositivity.KST.Comparison.diagonalRowDesc_unique
#print axioms SerrePositivity.KST.Comparison.diagonalRowDesc_unique


-- DiagonalRowEvaluation.lean

#check @SerrePositivity.KST.Comparison.diagonalRowEvaluation
#print axioms SerrePositivity.KST.Comparison.diagonalRowEvaluation

#check @SerrePositivity.KST.Comparison.diagonalRowEvaluation_naturality
#print axioms SerrePositivity.KST.Comparison.diagonalRowEvaluation_naturality

#check @SerrePositivity.KST.Comparison.diagonalRowEvaluation_dinaturality
#print axioms SerrePositivity.KST.Comparison.diagonalRowEvaluation_dinaturality

#check @SerrePositivity.KST.Comparison.diagonalRowEvaluation_identity
#print axioms SerrePositivity.KST.Comparison.diagonalRowEvaluation_identity


-- DiagramArrowFibers.lean

#check @SerrePositivity.KST.Comparison.diagramArrowFiber
#print axioms SerrePositivity.KST.Comparison.diagramArrowFiber

#check @SerrePositivity.KST.Comparison.diagramArrowFiberComparison
#print axioms SerrePositivity.KST.Comparison.diagramArrowFiberComparison

#check @SerrePositivity.KST.Comparison.diagramArrowFiberComparison_isIso_iff
#print axioms SerrePositivity.KST.Comparison.diagramArrowFiberComparison_isIso_iff

#check @SerrePositivity.KST.Comparison.diagramArrowFiber_kanComplex
#print axioms SerrePositivity.KST.Comparison.diagramArrowFiber_kanComplex


-- DiagramBaseChange.lean

#check @SerrePositivity.KST.Comparison.diagramPullback_app_isPullback
#print axioms SerrePositivity.KST.Comparison.diagramPullback_app_isPullback

#check @SerrePositivity.KST.Comparison.diagramPullback_fst_rlp
#print axioms SerrePositivity.KST.Comparison.diagramPullback_fst_rlp

#check @SerrePositivity.KST.Comparison.diagramPullback_snd_localized_isIso
#print axioms SerrePositivity.KST.Comparison.diagramPullback_snd_localized_isIso

#check @SerrePositivity.KST.Comparison.diagramPullback_arrowSquare_iff
#print axioms SerrePositivity.KST.Comparison.diagramPullback_arrowSquare_iff


-- DiagramExInfinity.lean

#check @SerrePositivity.KST.Comparison.diagramExInfinityUnit
#print axioms SerrePositivity.KST.Comparison.diagramExInfinityUnit

#check @SerrePositivity.KST.Comparison.diagramExInfinityUnit_naturality
#print axioms SerrePositivity.KST.Comparison.diagramExInfinityUnit_naturality

#check @SerrePositivity.KST.Comparison.diagramExInfinityUnit_localized_isIso
#print axioms SerrePositivity.KST.Comparison.diagramExInfinityUnit_localized_isIso

#check @SerrePositivity.KST.Comparison.diagramExInfinity_arrowSquare_iff
#print axioms SerrePositivity.KST.Comparison.diagramExInfinity_arrowSquare_iff


-- DiagramKanReplacement.lean

#check @SerrePositivity.KST.Comparison.diagramKanMiddle
#print axioms SerrePositivity.KST.Comparison.diagramKanMiddle

#check @SerrePositivity.KST.Comparison.diagramKanUnit
#print axioms SerrePositivity.KST.Comparison.diagramKanUnit

#check @SerrePositivity.KST.Comparison.diagramKanProjection
#print axioms SerrePositivity.KST.Comparison.diagramKanProjection

#check @SerrePositivity.KST.Comparison.diagramKan_fac
#print axioms SerrePositivity.KST.Comparison.diagramKan_fac

#check @SerrePositivity.KST.Comparison.diagramKanUnit_anodyne
#print axioms SerrePositivity.KST.Comparison.diagramKanUnit_anodyne

#check @SerrePositivity.KST.Comparison.diagramKanProjection_rlp
#print axioms SerrePositivity.KST.Comparison.diagramKanProjection_rlp


-- DoldKanGL.lean

#check @SerrePositivity.KST.Comparison.unitsPreimage
#print axioms SerrePositivity.KST.Comparison.unitsPreimage

#check @SerrePositivity.KST.Comparison.evalZeroUnits
#print axioms SerrePositivity.KST.Comparison.evalZeroUnits

#check @SerrePositivity.KST.Comparison.one_add_X_mem_evalZeroUnits
#print axioms SerrePositivity.KST.Comparison.one_add_X_mem_evalZeroUnits

#check @SerrePositivity.KST.Comparison.not_isUnit_one_add_X
#print axioms SerrePositivity.KST.Comparison.not_isUnit_one_add_X

#check @SerrePositivity.KST.Comparison.one_add_X_no_right_inverse
#print axioms SerrePositivity.KST.Comparison.one_add_X_no_right_inverse

#check @SerrePositivity.KST.Comparison.matrixToComponents
#print axioms SerrePositivity.KST.Comparison.matrixToComponents

#check @SerrePositivity.KST.Comparison.matrixToComponents_natural
#print axioms SerrePositivity.KST.Comparison.matrixToComponents_natural

#check @SerrePositivity.KST.Comparison.hatGLSubmonoid
#print axioms SerrePositivity.KST.Comparison.hatGLSubmonoid

#check @SerrePositivity.KST.Comparison.hatGLPullback
#print axioms SerrePositivity.KST.Comparison.hatGLPullback

#check @SerrePositivity.KST.Comparison.hatGLMonoidObject
#print axioms SerrePositivity.KST.Comparison.hatGLMonoidObject


-- DoubleMappingCylinder.lean

#check @_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints
#print axioms _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints

#check @_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder
#print axioms _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder

#check @_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle
#print axioms _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle

#check @_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left
#print axioms _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left

#check @_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right
#print axioms _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right

#check @_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_zero
#print axioms _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_zero

#check @_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_one
#print axioms _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_one


-- DoubleMappingCylinderCollapse.lean

#check @SerrePositivity.KST.Comparison.doubleMappingCylinderCollapse
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinderCollapse

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_middle_collapse
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_middle_collapse

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_left_collapse
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_left_collapse

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_right_collapse
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_right_collapse

#check @SerrePositivity.KST.Comparison.mappingCylinderToDouble_collapse
#print axioms SerrePositivity.KST.Comparison.mappingCylinderToDouble_collapse

#check @SerrePositivity.KST.Comparison.doubleMappingCylinderCollapse_localized_isIso
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinderCollapse_localized_isIso


-- DoubleMappingCylinderDesc.lean

#check @_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderDesc
#print axioms _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderDesc

#check @_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_desc
#print axioms _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_desc

#check @_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_desc
#print axioms _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_desc

#check @_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_desc
#print axioms _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_desc

#check @_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DoubleMappingCylinderDesc.doubleMappingCylinder_hom_ext
#print axioms _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DoubleMappingCylinderDesc.doubleMappingCylinder_hom_ext


-- DoubleMappingCylinderEquivalence.lean

#check @SerrePositivity.KST.Comparison.cylinderEndpoints_naturality
#print axioms SerrePositivity.KST.Comparison.cylinderEndpoints_naturality

#check @SerrePositivity.KST.Comparison.doubleMappingCylinderMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinderMap_localized_isIso


-- DoubleMappingCylinderMap.lean

#check @_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap
#print axioms _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap

#check @_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_map
#print axioms _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_map

#check @_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_map
#print axioms _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_map

#check @_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_map
#print axioms _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_map

#check @_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DoubleMappingCylinderMap.doubleMappingCylinder_hom_ext
#print axioms _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DoubleMappingCylinderMap.doubleMappingCylinder_hom_ext

#check @_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap_id
#print axioms _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap_id

#check @_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap_comp
#print axioms _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap_comp


-- DoubleSubdivisionAdjunction.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.doubleSubdivisionHomEquiv
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.doubleSubdivisionHomEquiv

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.doubleSubdivisionHomEquiv_naturality_left
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.doubleSubdivisionHomEquiv_naturality_left

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.doubleSubdivisionHomEquiv_lastVertex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.doubleSubdivisionHomEquiv_lastVertex


-- DoubleSubdivisionHornBoundary.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.doubleSubdivisionHornMap_boundary
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.doubleSubdivisionHornMap_boundary


-- DoubleSubdivisionHornMap.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.doubleSubdivisionHornMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.doubleSubdivisionHornMap

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.doubleSubdivisionHornMap_ι
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.doubleSubdivisionHornMap_ι


-- ExComplexity.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexity
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexity

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexity_mono
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexity_mono

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexity_last
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexity_last

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexity_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexity_zero

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexityLevel
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexityLevel

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexityLevel_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexityLevel_mem

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexityLevel_le_iff
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexityLevel_le_iff

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexityLevel_zero_iff
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexityLevel_zero_iff


-- ExDegeneracyExpansion.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexity_front_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexity_front_face

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_front_degeneracy
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_front_degeneracy

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_rear_degeneracy
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_rear_degeneracy


-- ExDoubleHornFiller.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exDoubleUniversalHornFiller
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exDoubleUniversalHornFiller

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exDoubleUniversalHornFiller_boundary
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exDoubleUniversalHornFiller_boundary

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exDoubleHornFiller
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exDoubleHornFiller

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exDoubleHornFiller_boundary
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exDoubleHornFiller_boundary


-- ExDoublePairing.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_double
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_double

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_double_degenerate
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_double_degenerate

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_notMem_range_of_nonDegenerate
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_notMem_range_of_nonDegenerate


-- ExExpansionFaces.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_front_complexity
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_front_complexity

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_rear_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_rear_face


-- ExExpansionSmallComplexity.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_eq_degeneracy_of_complexity_lt
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_eq_degeneracy_of_complexity_lt

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_degenerate_of_complexity_lt
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_degenerate_of_complexity_lt


-- ExInfinity.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exIterate
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exIterate

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exIterate_preservesFiniteLimits
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exIterate_preservesFiniteLimits

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exSequence
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exSequence

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exSequence_flip_preservesFiniteLimits
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exSequence_flip_preservesFiniteLimits

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_preservesFiniteLimits
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_preservesFiniteLimits

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityStage
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityStage

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit


-- ExInfinityAnodyne.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityAnodyneSequence
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityAnodyneSequence

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne


-- ExInfinityBar.lean

#check @SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_bar_localized_isIso
#print axioms SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_bar_localized_isIso


-- ExInfinityFibrations.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exIterate_map_rlp
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exIterate_map_rlp

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_rlp
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_rlp


-- ExInfinityGrouplike.lean

#check @SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_componentsMulEquiv
#print axioms SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_componentsMulEquiv

#check @SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_isGrouplike
#print axioms SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_isGrouplike


-- ExInfinityHomotopyPullback.lean

#check @SerrePositivity.KST.Comparison.isHomotopyPullback_exInfinity_iff
#print axioms SerrePositivity.KST.Comparison.isHomotopyPullback_exInfinity_iff


-- ExInfinityKan.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_hornFilling
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_hornFilling

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex


-- ExInfinityLocalization.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_preservesMonomorphisms
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_preservesMonomorphisms

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_localized_isIso
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_localized_isIso

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityLocalizedUnitIso
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityLocalizedUnitIso

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_localized_isIso_iff
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_localized_isIso_iff


-- ExInfinityMonoidal.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_monoidal
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_monoidal

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_isMonoidal
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_isMonoidal

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityMonoidFunctor
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityMonoidFunctor

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityMonoidUnit
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityMonoidUnit

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityMonoid_kanComplex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityMonoid_kanComplex

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityMonoidUnit_hom
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityMonoidUnit_hom

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityMonoidUnit_localized_isIso
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityMonoidUnit_localized_isIso


-- ExInfinitySimplicialMonoid.lean

#check @SerrePositivity.KST.Comparison.simplicialMonoidInternalUnit
#print axioms SerrePositivity.KST.Comparison.simplicialMonoidInternalUnit

#check @SerrePositivity.KST.Comparison.exInfinitySimplicialMonoidFunctor
#print axioms SerrePositivity.KST.Comparison.exInfinitySimplicialMonoidFunctor

#check @SerrePositivity.KST.Comparison.exInfinitySimplicialMonoidUnit
#print axioms SerrePositivity.KST.Comparison.exInfinitySimplicialMonoidUnit

#check @SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_space
#print axioms SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_space

#check @SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_kanComplex
#print axioms SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_kanComplex

#check @SerrePositivity.KST.Comparison.exInfinitySimplicialMonoidUnit_space
#print axioms SerrePositivity.KST.Comparison.exInfinitySimplicialMonoidUnit_space

#check @SerrePositivity.KST.Comparison.exInfinitySimplicialMonoidUnit_localized_isIso
#print axioms SerrePositivity.KST.Comparison.exInfinitySimplicialMonoidUnit_localized_isIso


-- ExInfinityStages.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_finite_factorization
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_finite_factorization

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityStage_succ
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityStage_succ


-- ExPairingBijection.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exTypeOne
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exTypeOne

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_mem_typeOne
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_mem_typeOne

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_mem_typeTwo_of_typeOne
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_mem_typeTwo_of_typeOne

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingEquiv
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingEquiv

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingEquiv_apply
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingEquiv_apply


-- ExPairingCore.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingCore
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingCore

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingCore_isProper
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingCore_isProper

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairing
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairing


-- ExPairingFaceRank.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_notMem_typeTwo
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_notMem_typeTwo

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_face_rank_lt_succ
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_face_rank_lt_succ

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_face_rank_lt
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_face_rank_lt


-- ExPairingFaceUniqueness.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_front_ne_source
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_front_ne_source

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_rear_ne_source
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_rear_ne_source

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_face_unique_succ
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_face_unique_succ


-- ExPairingNondegenerate.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_mem_degenerate
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_mem_degenerate

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_mem_degenerate
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_mem_degenerate

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_nonDegenerate_source
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_nonDegenerate_source


-- ExPairingProperness.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingImage
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingImage

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exTypeTwo
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exTypeTwo

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_face_unique
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_face_unique

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_nonDegenerate_target
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_nonDegenerate_target

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_isUniquelyCodimOneFace
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_isUniquelyCodimOneFace


-- ExPairingRegular.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingWeakRank
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingWeakRank

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingCore_isRegular
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingCore_isRegular

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairing_isRegular
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairing_isRegular


-- ExPairingStep.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_face

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_complexity
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exExpansion_complexity

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexity_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exComplexity_face

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_injective
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_injective

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_complexity_iff
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_complexity_iff

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_complexityLevel
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_complexityLevel

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_mem_image_iff
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exPairingStep_mem_image_iff


-- ExUnit.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitAt
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitAt

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitAt_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitAt_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnit
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnit

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitAt_mono
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitAt_mono


-- ExUnitAnodyne.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitRange_anodyne
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitRange_anodyne

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitAt_anodyne
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exUnitAt_anodyne


-- FaceIntervals.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace_injective
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace_injective

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace_of_below
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace_of_below

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace_initialSegment_of_below
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace_initialSegment_of_below


-- FatAttachmentSpan.lean

#check @SerrePositivity.KST.Comparison.fatAttachmentSpan
#print axioms SerrePositivity.KST.Comparison.fatAttachmentSpan

#check @SerrePositivity.KST.Comparison.fatAttachmentSpan_snd_mono
#print axioms SerrePositivity.KST.Comparison.fatAttachmentSpan_snd_mono

#check @SerrePositivity.KST.Comparison.fatAttachmentCocone
#print axioms SerrePositivity.KST.Comparison.fatAttachmentCocone

#check @SerrePositivity.KST.Comparison.fatAttachmentCoconeIsColimit
#print axioms SerrePositivity.KST.Comparison.fatAttachmentCoconeIsColimit

#check @SerrePositivity.KST.Comparison.fatAttachmentSpanMap
#print axioms SerrePositivity.KST.Comparison.fatAttachmentSpanMap

#check @SerrePositivity.KST.Comparison.fatAttachmentCocone_map
#print axioms SerrePositivity.KST.Comparison.fatAttachmentCocone_map


-- FatBoundaryCriterion.lean

#check @SerrePositivity.KST.Comparison.simplexImage_len_le_iff_not_epi
#print axioms SerrePositivity.KST.Comparison.simplexImage_len_le_iff_not_epi

#check @SerrePositivity.KST.Comparison.fatRealizationInclusion_mem_skeleton_iff_boundary
#print axioms SerrePositivity.KST.Comparison.fatRealizationInclusion_mem_skeleton_iff_boundary


-- FatBoundaryHomotopyPullback.lean

#check @SerrePositivity.KST.Comparison.fatBoundaryAttachment_homotopyPullback
#print axioms SerrePositivity.KST.Comparison.fatBoundaryAttachment_homotopyPullback


-- FatDegreeNormalization.lean

#check @SerrePositivity.KST.Comparison.fatDegreeCofork
#print axioms SerrePositivity.KST.Comparison.fatDegreeCofork

#check @SerrePositivity.KST.Comparison.fatDegreeCoforkIsColimit
#print axioms SerrePositivity.KST.Comparison.fatDegreeCoforkIsColimit

#check @SerrePositivity.KST.Comparison.fatRowNormalize
#print axioms SerrePositivity.KST.Comparison.fatRowNormalize

#check @SerrePositivity.KST.Comparison.fatRowNormalize_condition
#print axioms SerrePositivity.KST.Comparison.fatRowNormalize_condition

#check @SerrePositivity.KST.Comparison.fatDegreeNormalize
#print axioms SerrePositivity.KST.Comparison.fatDegreeNormalize

#check @SerrePositivity.KST.Comparison.fatDegreeNormalize_π
#print axioms SerrePositivity.KST.Comparison.fatDegreeNormalize_π

#check @SerrePositivity.KST.Comparison.fatDegreeNormalize_inclusion
#print axioms SerrePositivity.KST.Comparison.fatDegreeNormalize_inclusion


-- FatDiagonalComparison.lean

#check @SerrePositivity.KST.Comparison.fatRealizationToDiagonal_realize
#print axioms SerrePositivity.KST.Comparison.fatRealizationToDiagonal_realize

#check @SerrePositivity.KST.Comparison.fatFreeColumnsIso_augmentation
#print axioms SerrePositivity.KST.Comparison.fatFreeColumnsIso_augmentation

#check @SerrePositivity.KST.Comparison.fatRealizationToDiagonal_localized_isIso
#print axioms SerrePositivity.KST.Comparison.fatRealizationToDiagonal_localized_isIso


-- FatFreeColumnsIso.lean

#check @SerrePositivity.KST.Comparison.fatFreeColumnsDegreeIso_naturality
#print axioms SerrePositivity.KST.Comparison.fatFreeColumnsDegreeIso_naturality

#check @SerrePositivity.KST.Comparison.fatFreeColumnsIso
#print axioms SerrePositivity.KST.Comparison.fatFreeColumnsIso


-- FatNormalForm.lean

#check @SerrePositivity.KST.Comparison.FatNormalForm
#print axioms SerrePositivity.KST.Comparison.FatNormalForm

#check @SerrePositivity.KST.Comparison.fatNormalize
#print axioms SerrePositivity.KST.Comparison.fatNormalize

#check @SerrePositivity.KST.Comparison.fatNormalize_eq_of_factorization
#print axioms SerrePositivity.KST.Comparison.fatNormalize_eq_of_factorization

#check @SerrePositivity.KST.Comparison.fatNormalize_face
#print axioms SerrePositivity.KST.Comparison.fatNormalize_face

#check @SerrePositivity.KST.Comparison.fatNormalize_of_normalForm
#print axioms SerrePositivity.KST.Comparison.fatNormalize_of_normalForm


-- FatNormalFormAction.lean

#check @SerrePositivity.KST.Comparison.fatNormalFormRealize_action
#print axioms SerrePositivity.KST.Comparison.fatNormalFormRealize_action

#check @SerrePositivity.KST.Comparison.fatDegreeNormalize_action
#print axioms SerrePositivity.KST.Comparison.fatDegreeNormalize_action

#check @SerrePositivity.KST.Comparison.fatNormalDegree_action_le
#print axioms SerrePositivity.KST.Comparison.fatNormalDegree_action_le

#check @SerrePositivity.KST.Comparison.fatNormalDegree_le
#print axioms SerrePositivity.KST.Comparison.fatNormalDegree_le


-- FatNormalFormEquiv.lean

#check @SerrePositivity.KST.Comparison.fatNormalFormRealize
#print axioms SerrePositivity.KST.Comparison.fatNormalFormRealize

#check @SerrePositivity.KST.Comparison.fatNormalFormRealize_normalize
#print axioms SerrePositivity.KST.Comparison.fatNormalFormRealize_normalize

#check @SerrePositivity.KST.Comparison.fatDegreeNormalize_realize
#print axioms SerrePositivity.KST.Comparison.fatDegreeNormalize_realize

#check @SerrePositivity.KST.Comparison.fatNormalFormRealize_degreeNormalize
#print axioms SerrePositivity.KST.Comparison.fatNormalFormRealize_degreeNormalize

#check @SerrePositivity.KST.Comparison.fatNormalFormEquiv
#print axioms SerrePositivity.KST.Comparison.fatNormalFormEquiv


-- FatNormalFormMap.lean

#check @SerrePositivity.KST.Comparison.fatNormalFormMap
#print axioms SerrePositivity.KST.Comparison.fatNormalFormMap

#check @SerrePositivity.KST.Comparison.fatNormalize_map
#print axioms SerrePositivity.KST.Comparison.fatNormalize_map

#check @SerrePositivity.KST.Comparison.fatNormalFormRealize_map
#print axioms SerrePositivity.KST.Comparison.fatNormalFormRealize_map

#check @SerrePositivity.KST.Comparison.fatDegreeNormalize_map
#print axioms SerrePositivity.KST.Comparison.fatDegreeNormalize_map


-- FatRealization.lean

#check @SerrePositivity.KST.Comparison.SimplexFace
#print axioms SerrePositivity.KST.Comparison.SimplexFace

#check @SerrePositivity.KST.Comparison.fatRowObject
#print axioms SerrePositivity.KST.Comparison.fatRowObject

#check @SerrePositivity.KST.Comparison.fatRelationObject
#print axioms SerrePositivity.KST.Comparison.fatRelationObject

#check @SerrePositivity.KST.Comparison.fatRelationLeft
#print axioms SerrePositivity.KST.Comparison.fatRelationLeft

#check @SerrePositivity.KST.Comparison.fatRelationRight
#print axioms SerrePositivity.KST.Comparison.fatRelationRight

#check @SerrePositivity.KST.Comparison.fatRealization
#print axioms SerrePositivity.KST.Comparison.fatRealization

#check @SerrePositivity.KST.Comparison.fatRealizationInclusion
#print axioms SerrePositivity.KST.Comparison.fatRealizationInclusion

#check @SerrePositivity.KST.Comparison.fatRealizationInclusion_face
#print axioms SerrePositivity.KST.Comparison.fatRealizationInclusion_face


-- FatRealizationDesc.lean

#check @SerrePositivity.KST.Comparison.fatRealizationDesc
#print axioms SerrePositivity.KST.Comparison.fatRealizationDesc

#check @SerrePositivity.KST.Comparison.fatRealizationInclusion_desc
#print axioms SerrePositivity.KST.Comparison.fatRealizationInclusion_desc

#check @SerrePositivity.KST.Comparison.fatRealization_hom_ext
#print axioms SerrePositivity.KST.Comparison.fatRealization_hom_ext

#check @SerrePositivity.KST.Comparison.fatRealizationToDiagonal
#print axioms SerrePositivity.KST.Comparison.fatRealizationToDiagonal

#check @SerrePositivity.KST.Comparison.fatRealizationInclusion_toDiagonal
#print axioms SerrePositivity.KST.Comparison.fatRealizationInclusion_toDiagonal


-- FatRealizationFunctor.lean

#check @SerrePositivity.KST.Comparison.fatRealizationMap
#print axioms SerrePositivity.KST.Comparison.fatRealizationMap

#check @SerrePositivity.KST.Comparison.fatRealizationInclusion_map
#print axioms SerrePositivity.KST.Comparison.fatRealizationInclusion_map

#check @SerrePositivity.KST.Comparison.fatRealizationFunctor
#print axioms SerrePositivity.KST.Comparison.fatRealizationFunctor

#check @SerrePositivity.KST.Comparison.fatRealizationToDiagonalNatTrans
#print axioms SerrePositivity.KST.Comparison.fatRealizationToDiagonalNatTrans


-- FatRealizationHomotopyPullback.lean

#check @SerrePositivity.KST.Comparison.fatRealizationInclusion_homotopyPullback
#print axioms SerrePositivity.KST.Comparison.fatRealizationInclusion_homotopyPullback


-- FatRealizationInvariance.lean

#check @SerrePositivity.KST.Comparison.fatRealizationMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.fatRealizationMap_localized_isIso


-- FatRealizationMono.lean

#check @SerrePositivity.KST.Comparison.fatNormalFormMap_injective
#print axioms SerrePositivity.KST.Comparison.fatNormalFormMap_injective

#check @SerrePositivity.KST.Comparison.fatRealizationMap_mono
#print axioms SerrePositivity.KST.Comparison.fatRealizationMap_mono


-- FatRowComplement.lean

#check @SerrePositivity.KST.Comparison.fatNormalFormRealize_eq_row
#print axioms SerrePositivity.KST.Comparison.fatNormalFormRealize_eq_row

#check @SerrePositivity.KST.Comparison.fatRealizationInclusion_injective_off_boundary
#print axioms SerrePositivity.KST.Comparison.fatRealizationInclusion_injective_off_boundary

#check @SerrePositivity.KST.Comparison.fatRealizationInclusion_injective_off_boundary_range
#print axioms SerrePositivity.KST.Comparison.fatRealizationInclusion_injective_off_boundary_range


-- FatSkeleton.lean

#check @SerrePositivity.KST.Comparison.fatSkeleton
#print axioms SerrePositivity.KST.Comparison.fatSkeleton

#check @SerrePositivity.KST.Comparison.fatSkeleton_monotone
#print axioms SerrePositivity.KST.Comparison.fatSkeleton_monotone

#check @SerrePositivity.KST.Comparison.fatSkeleton_obj_eq_univ
#print axioms SerrePositivity.KST.Comparison.fatSkeleton_obj_eq_univ

#check @SerrePositivity.KST.Comparison.iSup_fatSkeleton_eq_top
#print axioms SerrePositivity.KST.Comparison.iSup_fatSkeleton_eq_top

#check @SerrePositivity.KST.Comparison.fatRealizationInclusion_mem_skeleton
#print axioms SerrePositivity.KST.Comparison.fatRealizationInclusion_mem_skeleton


-- FatSkeletonAttachment.lean

#check @SerrePositivity.KST.Comparison.fatSkeletonStep
#print axioms SerrePositivity.KST.Comparison.fatSkeletonStep

#check @SerrePositivity.KST.Comparison.fatSkeletonStep_ι
#print axioms SerrePositivity.KST.Comparison.fatSkeletonStep_ι

#check @SerrePositivity.KST.Comparison.fatBoundaryAttachment
#print axioms SerrePositivity.KST.Comparison.fatBoundaryAttachment

#check @SerrePositivity.KST.Comparison.fatBoundaryAttachment_ι
#print axioms SerrePositivity.KST.Comparison.fatBoundaryAttachment_ι

#check @SerrePositivity.KST.Comparison.fatBoundaryAttachment_isPullback
#print axioms SerrePositivity.KST.Comparison.fatBoundaryAttachment_isPullback


-- FatSkeletonColimit.lean

#check @SerrePositivity.KST.Comparison.fatSkeletonSequence
#print axioms SerrePositivity.KST.Comparison.fatSkeletonSequence

#check @SerrePositivity.KST.Comparison.fatSkeletonCocone
#print axioms SerrePositivity.KST.Comparison.fatSkeletonCocone

#check @SerrePositivity.KST.Comparison.fatSkeletonCoconeIsColimit
#print axioms SerrePositivity.KST.Comparison.fatSkeletonCoconeIsColimit


-- FatSkeletonGeneralComparison.lean

#check @SerrePositivity.KST.Comparison.fatSkeletonRow_general_homotopyPullback
#print axioms SerrePositivity.KST.Comparison.fatSkeletonRow_general_homotopyPullback


-- FatSkeletonHomotopyPullback.lean

#check @SerrePositivity.KST.Comparison.fatSkeletonRow_homotopyPullback
#print axioms SerrePositivity.KST.Comparison.fatSkeletonRow_homotopyPullback


-- FatSkeletonInvariance.lean

#check @SerrePositivity.KST.Comparison.fatSkeletonMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.fatSkeletonMap_localized_isIso


-- FatSkeletonMaps.lean

#check @SerrePositivity.KST.Comparison.fatSkeletonRow
#print axioms SerrePositivity.KST.Comparison.fatSkeletonRow

#check @SerrePositivity.KST.Comparison.fatSkeletonRow_ι
#print axioms SerrePositivity.KST.Comparison.fatSkeletonRow_ι

#check @SerrePositivity.KST.Comparison.fatSkeletonMap
#print axioms SerrePositivity.KST.Comparison.fatSkeletonMap

#check @SerrePositivity.KST.Comparison.fatSkeletonMap_ι
#print axioms SerrePositivity.KST.Comparison.fatSkeletonMap_ι

#check @SerrePositivity.KST.Comparison.fatSkeletonFunctor
#print axioms SerrePositivity.KST.Comparison.fatSkeletonFunctor

#check @SerrePositivity.KST.Comparison.fatSkeletonInclusion
#print axioms SerrePositivity.KST.Comparison.fatSkeletonInclusion


-- FatSkeletonPushout.lean

#check @SerrePositivity.KST.Comparison.fatSkeletonStep_row_jointly_surjective
#print axioms SerrePositivity.KST.Comparison.fatSkeletonStep_row_jointly_surjective

#check @SerrePositivity.KST.Comparison.fatSkeleton_isPushout
#print axioms SerrePositivity.KST.Comparison.fatSkeleton_isPushout


-- FatSkeletonRowRelations.lean

#check @SerrePositivity.KST.Comparison.fatSkeletonRowOfLE
#print axioms SerrePositivity.KST.Comparison.fatSkeletonRowOfLE

#check @SerrePositivity.KST.Comparison.fatSkeletonRowOfLE_ι
#print axioms SerrePositivity.KST.Comparison.fatSkeletonRowOfLE_ι

#check @SerrePositivity.KST.Comparison.fatSkeletonRowOfLE_map
#print axioms SerrePositivity.KST.Comparison.fatSkeletonRowOfLE_map

#check @SerrePositivity.KST.Comparison.fatBoundaryAttachment_map
#print axioms SerrePositivity.KST.Comparison.fatBoundaryAttachment_map

#check @SerrePositivity.KST.Comparison.fatSkeletonRowOfLE_face
#print axioms SerrePositivity.KST.Comparison.fatSkeletonRowOfLE_face

#check @SerrePositivity.KST.Comparison.fatBoundaryAttachment_face
#print axioms SerrePositivity.KST.Comparison.fatBoundaryAttachment_face


-- FatSkeletonSuccessor.lean

#check @SerrePositivity.KST.Comparison.fatSkeletonStep_map
#print axioms SerrePositivity.KST.Comparison.fatSkeletonStep_map

#check @SerrePositivity.KST.Comparison.fatSkeleton_successor_homotopyPullback
#print axioms SerrePositivity.KST.Comparison.fatSkeleton_successor_homotopyPullback


-- FatSkeletonTail.lean

#check @SerrePositivity.KST.Comparison.natTailFunctor
#print axioms SerrePositivity.KST.Comparison.natTailFunctor

#check @SerrePositivity.KST.Comparison.natTailFunctor_final
#print axioms SerrePositivity.KST.Comparison.natTailFunctor_final

#check @SerrePositivity.KST.Comparison.fatSkeletonTail
#print axioms SerrePositivity.KST.Comparison.fatSkeletonTail

#check @SerrePositivity.KST.Comparison.fatSkeletonTailCocone
#print axioms SerrePositivity.KST.Comparison.fatSkeletonTailCocone

#check @SerrePositivity.KST.Comparison.fatSkeletonTailCoconeIsColimit
#print axioms SerrePositivity.KST.Comparison.fatSkeletonTailCoconeIsColimit

#check @SerrePositivity.KST.Comparison.fatSkeletonTailMap
#print axioms SerrePositivity.KST.Comparison.fatSkeletonTailMap

#check @SerrePositivity.KST.Comparison.fatSkeletonTailRow
#print axioms SerrePositivity.KST.Comparison.fatSkeletonTailRow

#check @SerrePositivity.KST.Comparison.fatSkeletonTailRow_map
#print axioms SerrePositivity.KST.Comparison.fatSkeletonTailRow_map


-- FatSkeletonZero.lean

#check @SerrePositivity.KST.Comparison.fatSkeletonRow_zero_isIso
#print axioms SerrePositivity.KST.Comparison.fatSkeletonRow_zero_isIso


-- FiberCoefficientAdjunction.lean

#check @SerrePositivity.KST.Comparison.fiberCoefficientHomFunctor
#print axioms SerrePositivity.KST.Comparison.fiberCoefficientHomFunctor

#check @SerrePositivity.KST.Comparison.fiberCoefficientProjection_eq
#print axioms SerrePositivity.KST.Comparison.fiberCoefficientProjection_eq

#check @SerrePositivity.KST.Comparison.fiberCoefficientLift
#print axioms SerrePositivity.KST.Comparison.fiberCoefficientLift

#check @SerrePositivity.KST.Comparison.fiberCoefficientDesc
#print axioms SerrePositivity.KST.Comparison.fiberCoefficientDesc

#check @SerrePositivity.KST.Comparison.fiberCoefficientSigmaReassemble
#print axioms SerrePositivity.KST.Comparison.fiberCoefficientSigmaReassemble

#check @SerrePositivity.KST.Comparison.fiberCoefficientHomEquiv
#print axioms SerrePositivity.KST.Comparison.fiberCoefficientHomEquiv

#check @SerrePositivity.KST.Comparison.fiberCoefficientHomEquiv_naturality
#print axioms SerrePositivity.KST.Comparison.fiberCoefficientHomEquiv_naturality

#check @SerrePositivity.KST.Comparison.fiberCoefficientFunctor
#print axioms SerrePositivity.KST.Comparison.fiberCoefficientFunctor

#check @SerrePositivity.KST.Comparison.fiberCoefficientAdjunction
#print axioms SerrePositivity.KST.Comparison.fiberCoefficientAdjunction

#check @SerrePositivity.KST.Comparison.fiberCoefficientFunctor_isLeftAdjoint
#print axioms SerrePositivity.KST.Comparison.fiberCoefficientFunctor_isLeftAdjoint


-- FiberCoefficientMaps.lean

#check @SerrePositivity.KST.Comparison.overTypeMap_base
#print axioms SerrePositivity.KST.Comparison.overTypeMap_base

#check @SerrePositivity.KST.Comparison.fiberCoefficientFunctor_map_ι
#print axioms SerrePositivity.KST.Comparison.fiberCoefficientFunctor_map_ι

#check @SerrePositivity.KST.Comparison.fiberCoefficientFunctor_map_factorization
#print axioms SerrePositivity.KST.Comparison.fiberCoefficientFunctor_map_factorization

#check @SerrePositivity.KST.Comparison.fiberCoefficientFunctor_preservesMonomorphisms
#print axioms SerrePositivity.KST.Comparison.fiberCoefficientFunctor_preservesMonomorphisms


-- FiberwiseAnodyne.lean

#check @SerrePositivity.KST.Comparison.pointTensorIso_fst
#print axioms SerrePositivity.KST.Comparison.pointTensorIso_fst

#check @SerrePositivity.KST.Comparison.anodyne_fiberwise_homotopy
#print axioms SerrePositivity.KST.Comparison.anodyne_fiberwise_homotopy

#check @SerrePositivity.KST.Comparison.anodyne_fibration_retraction
#print axioms SerrePositivity.KST.Comparison.anodyne_fibration_retraction


-- FiberwisePullback.lean

#check @SerrePositivity.KST.Comparison.pullbackMapOver
#print axioms SerrePositivity.KST.Comparison.pullbackMapOver

#check @SerrePositivity.KST.Comparison.pullbackMapOver_fst
#print axioms SerrePositivity.KST.Comparison.pullbackMapOver_fst

#check @SerrePositivity.KST.Comparison.pullbackMapOver_snd
#print axioms SerrePositivity.KST.Comparison.pullbackMapOver_snd

#check @SerrePositivity.KST.Comparison.pullbackMapOver_id
#print axioms SerrePositivity.KST.Comparison.pullbackMapOver_id

#check @SerrePositivity.KST.Comparison.pullbackHomotopyOver
#print axioms SerrePositivity.KST.Comparison.pullbackHomotopyOver


-- FibrantCospanInvariance.lean

#check @SerrePositivity.KST.Comparison.fibrantCospanMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.fibrantCospanMap_localized_isIso


-- FibrantPullbackComparison.lean

#check @SerrePositivity.KST.Comparison.fibrantPullbackComparison_isIso
#print axioms SerrePositivity.KST.Comparison.fibrantPullbackComparison_isIso

#check @SerrePositivity.KST.Comparison.isHomotopyPullback_of_fibration
#print axioms SerrePositivity.KST.Comparison.isHomotopyPullback_of_fibration


-- FibrantPullbackMap.lean

#check @SerrePositivity.KST.Comparison.pullbackMapBase_swap
#print axioms SerrePositivity.KST.Comparison.pullbackMapBase_swap

#check @SerrePositivity.KST.Comparison.pullbackMapBase_localized_isIso_of_fibration
#print axioms SerrePositivity.KST.Comparison.pullbackMapBase_localized_isIso_of_fibration

#check @SerrePositivity.KST.Comparison.pullbackMapBase_localized_isIso
#print axioms SerrePositivity.KST.Comparison.pullbackMapBase_localized_isIso

#check @SerrePositivity.KST.Comparison.pullbackMapBase_localized_isIso_of_kan_base
#print axioms SerrePositivity.KST.Comparison.pullbackMapBase_localized_isIso_of_kan_base


-- FibrantSquareCriterion.lean

#check @SerrePositivity.KST.Comparison.isHomotopyPullback_iff_strict_of_left_fibration
#print axioms SerrePositivity.KST.Comparison.isHomotopyPullback_iff_strict_of_left_fibration


-- FibrantTargetLifting.lean

#check @SerrePositivity.KST.Comparison.localizedMono_lifting_fibrantTarget
#print axioms SerrePositivity.KST.Comparison.localizedMono_lifting_fibrantTarget


-- FibrationLocality.lean

#check @SerrePositivity.KST.Comparison.lifting_of_pullbackFactorizations
#print axioms SerrePositivity.KST.Comparison.lifting_of_pullbackFactorizations

#check @SerrePositivity.KST.Comparison.kanFibration_of_pushoutCover
#print axioms SerrePositivity.KST.Comparison.kanFibration_of_pushoutCover


-- FiniteChainGreatest.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChain_exists_greatest
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChain_exists_greatest

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainGreatest
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainGreatest

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainGreatest_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainGreatest_mem

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.le_finiteChainGreatest
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.le_finiteChainGreatest

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainGreatest_map
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainGreatest_map

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainGreatest_eq_maximum
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainGreatest_eq_maximum


-- FiniteChainIntervals.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainMaximum_singleton
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainMaximum_singleton

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainMap_singleton
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainMap_singleton

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainInitialSegment_le_iff
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainInitialSegment_le_iff

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainInitialSegment_map
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainInitialSegment_map


-- FiniteChainUnion.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainOfFinset
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainOfFinset

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainSingleton
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainSingleton

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainUnion
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainUnion

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.PreservesFiniteChainUnion
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.PreservesFiniteChainUnion

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainUnion_ext
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainUnion_ext

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.PreservesFiniteChainUnion.comp
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.PreservesFiniteChainUnion.comp

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainMap_preservesUnion
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainMap_preservesUnion


-- FiniteCoverInduction.lean

#check @SerrePositivity.KST.Comparison.finiteSup_of_nonempty_intersections
#print axioms SerrePositivity.KST.Comparison.finiteSup_of_nonempty_intersections


-- FiniteOperationsFibrations.lean

#check @SerrePositivity.KST.Comparison.tensorRight_fst_isPullback
#print axioms SerrePositivity.KST.Comparison.tensorRight_fst_isPullback

#check @SerrePositivity.KST.Comparison.tensorRight_rlp
#print axioms SerrePositivity.KST.Comparison.tensorRight_rlp

#check @SerrePositivity.KST.Comparison.coproductMap_rlp
#print axioms SerrePositivity.KST.Comparison.coproductMap_rlp


-- FreeColumns.lean

#check @SerrePositivity.KST.Comparison.freeColumns
#print axioms SerrePositivity.KST.Comparison.freeColumns

#check @SerrePositivity.KST.Comparison.freeColumnsAugmentation
#print axioms SerrePositivity.KST.Comparison.freeColumnsAugmentation

#check @SerrePositivity.KST.Comparison.diagonalFlipIso
#print axioms SerrePositivity.KST.Comparison.diagonalFlipIso

#check @SerrePositivity.KST.Comparison.fatColumnNormalFormEquiv
#print axioms SerrePositivity.KST.Comparison.fatColumnNormalFormEquiv

#check @SerrePositivity.KST.Comparison.fatFreeColumnsDegreeIso
#print axioms SerrePositivity.KST.Comparison.fatFreeColumnsDegreeIso


-- FreeDegeneracies.lean

#check @SerrePositivity.KST.Comparison.discreteRowsFunctor
#print axioms SerrePositivity.KST.Comparison.discreteRowsFunctor

#check @SerrePositivity.KST.Comparison.discreteRowsDiagonalIso
#print axioms SerrePositivity.KST.Comparison.discreteRowsDiagonalIso

#check @SerrePositivity.KST.Comparison.freeDegeneracies
#print axioms SerrePositivity.KST.Comparison.freeDegeneracies

#check @SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation
#print axioms SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation

#check @SerrePositivity.KST.Comparison.freeDegeneraciesNormalForm
#print axioms SerrePositivity.KST.Comparison.freeDegeneraciesNormalForm


-- FreeDegeneraciesCalculations.lean

#check @SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation_realize
#print axioms SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation_realize

#check @SerrePositivity.KST.Comparison.freeDegeneraciesNormalForm_action
#print axioms SerrePositivity.KST.Comparison.freeDegeneraciesNormalForm_action

#check @SerrePositivity.KST.Comparison.freeDegeneracies_preservesMonomorphisms
#print axioms SerrePositivity.KST.Comparison.freeDegeneracies_preservesMonomorphisms


-- FreeDegeneraciesColimits.lean

#check @SerrePositivity.KST.Comparison.freeDegeneracyShapeDiagram_preservesColimits
#print axioms SerrePositivity.KST.Comparison.freeDegeneracyShapeDiagram_preservesColimits

#check @SerrePositivity.KST.Comparison.freeDegeneracies_preservesColimits
#print axioms SerrePositivity.KST.Comparison.freeDegeneracies_preservesColimits


-- FreeDegeneraciesEquivalence.lean

#check @SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation_localized_isIso
#print axioms SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation_localized_isIso


-- FreeDegeneracyShapeNaturality.lean

#check @SerrePositivity.KST.Comparison.freeDegeneracyShapeColimitIso_naturality
#print axioms SerrePositivity.KST.Comparison.freeDegeneracyShapeColimitIso_naturality

#check @SerrePositivity.KST.Comparison.freeDegeneracyShapeColimitNatIso
#print axioms SerrePositivity.KST.Comparison.freeDegeneracyShapeColimitNatIso


-- FreeDegeneracyShapes.lean

#check @SerrePositivity.KST.Comparison.FreeDegeneracyShape
#print axioms SerrePositivity.KST.Comparison.FreeDegeneracyShape

#check @SerrePositivity.KST.Comparison.freeDegeneracyShapeEquiv
#print axioms SerrePositivity.KST.Comparison.freeDegeneracyShapeEquiv

#check @SerrePositivity.KST.Comparison.freeDegeneracyShapeDiagram
#print axioms SerrePositivity.KST.Comparison.freeDegeneracyShapeDiagram

#check @SerrePositivity.KST.Comparison.freeDegeneracyShapeColimitIso
#print axioms SerrePositivity.KST.Comparison.freeDegeneracyShapeColimitIso


-- FreeStandardContraction.lean

#check @SerrePositivity.KST.Comparison.freeStandardAugmented
#print axioms SerrePositivity.KST.Comparison.freeStandardAugmented

#check @SerrePositivity.KST.Comparison.freeStandardExtraDegeneracy
#print axioms SerrePositivity.KST.Comparison.freeStandardExtraDegeneracy

#check @SerrePositivity.KST.Comparison.freeStandardAugmented_localized_isIso
#print axioms SerrePositivity.KST.Comparison.freeStandardAugmented_localized_isIso

#check @SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation_standard_localized_isIso
#print axioms SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation_standard_localized_isIso


-- FreeStandardNormalization.lean

#check @SerrePositivity.KST.Comparison.simplexConeZero_simplexMap
#print axioms SerrePositivity.KST.Comparison.simplexConeZero_simplexMap

#check @SerrePositivity.KST.Comparison.freeStandardPrepend_normalize
#print axioms SerrePositivity.KST.Comparison.freeStandardPrepend_normalize


-- FreeStandardPrepend.lean

#check @SerrePositivity.KST.Comparison.freeStandardPrependNormalForm
#print axioms SerrePositivity.KST.Comparison.freeStandardPrependNormalForm

#check @SerrePositivity.KST.Comparison.freeStandardPrepend
#print axioms SerrePositivity.KST.Comparison.freeStandardPrepend


-- FreeStandardPrependAction.lean

#check @SerrePositivity.KST.Comparison.freeStandardPrependNormalForm_action
#print axioms SerrePositivity.KST.Comparison.freeStandardPrependNormalForm_action


-- FreeStandardPrependFaces.lean

#check @SerrePositivity.KST.Comparison.freeStandardPrependNormalForm_δ_zero
#print axioms SerrePositivity.KST.Comparison.freeStandardPrependNormalForm_δ_zero

#check @SerrePositivity.KST.Comparison.freeStandardPrepend_δ_zero
#print axioms SerrePositivity.KST.Comparison.freeStandardPrepend_δ_zero

#check @SerrePositivity.KST.Comparison.freeStandardPrepend_naturality
#print axioms SerrePositivity.KST.Comparison.freeStandardPrepend_naturality


-- FreeStandardZeroVertex.lean

#check @SerrePositivity.KST.Comparison.freeStandardZeroNormalForm
#print axioms SerrePositivity.KST.Comparison.freeStandardZeroNormalForm

#check @SerrePositivity.KST.Comparison.freeStandardZeroVertex
#print axioms SerrePositivity.KST.Comparison.freeStandardZeroVertex

#check @SerrePositivity.KST.Comparison.freeStandardPrependNormalForm_δ_one
#print axioms SerrePositivity.KST.Comparison.freeStandardPrependNormalForm_δ_one


-- FunctorHomotopyPullbacks.lean

#check @SerrePositivity.KST.Comparison.isHomotopyPullback_map_of_preserves_factorizations
#print axioms SerrePositivity.KST.Comparison.isHomotopyPullback_map_of_preserves_factorizations


-- GLComponents.lean

#check @SerrePositivity.KST.Comparison.hatGLSpace
#print axioms SerrePositivity.KST.Comparison.hatGLSpace

#check @SerrePositivity.KST.Comparison.matrixToComponents_zero_entry
#print axioms SerrePositivity.KST.Comparison.matrixToComponents_zero_entry

#check @SerrePositivity.KST.Comparison.hatGLCoefficientEdge
#print axioms SerrePositivity.KST.Comparison.hatGLCoefficientEdge

#check @SerrePositivity.KST.Comparison.hatGLEdgeOfCoefficients
#print axioms SerrePositivity.KST.Comparison.hatGLEdgeOfCoefficients

#check @SerrePositivity.KST.Comparison.hatGLVertexUnit
#print axioms SerrePositivity.KST.Comparison.hatGLVertexUnit

#check @SerrePositivity.KST.Comparison.hatGLVertexUnit_edge
#print axioms SerrePositivity.KST.Comparison.hatGLVertexUnit_edge

#check @SerrePositivity.KST.Comparison.hatGLClassMap
#print axioms SerrePositivity.KST.Comparison.hatGLClassMap

#check @SerrePositivity.KST.Comparison.hatGLClassMap_injective
#print axioms SerrePositivity.KST.Comparison.hatGLClassMap_injective

#check @SerrePositivity.KST.Comparison.hatGLClassMap_surjective
#print axioms SerrePositivity.KST.Comparison.hatGLClassMap_surjective

#check @SerrePositivity.KST.Comparison.hatGLComponentsEquiv
#print axioms SerrePositivity.KST.Comparison.hatGLComponentsEquiv

#check @SerrePositivity.KST.Comparison.hatGLComponentsGroup
#print axioms SerrePositivity.KST.Comparison.hatGLComponentsGroup

#check @SerrePositivity.KST.Comparison.hatGLComponentsMulEquiv
#print axioms SerrePositivity.KST.Comparison.hatGLComponentsMulEquiv

#check @SerrePositivity.KST.Comparison.hatGLVertexUnit_mul
#print axioms SerrePositivity.KST.Comparison.hatGLVertexUnit_mul

#check @SerrePositivity.KST.Comparison.hatGL_mk_mul
#print axioms SerrePositivity.KST.Comparison.hatGL_mk_mul

#check @SerrePositivity.KST.Comparison.hatGL_mk_one
#print axioms SerrePositivity.KST.Comparison.hatGL_mk_one


-- GammaH0.lean

#check @SerrePositivity.KST.Comparison.sameUniverseLiftIso
#print axioms SerrePositivity.KST.Comparison.sameUniverseLiftIso

#check @SerrePositivity.KST.Comparison.gammaEndPinchedIso
#print axioms SerrePositivity.KST.Comparison.gammaEndPinchedIso

#check @SerrePositivity.KST.Comparison.gammaEndPiZeroH0Equiv
#print axioms SerrePositivity.KST.Comparison.gammaEndPiZeroH0Equiv

#check @SerrePositivity.KST.Comparison.gammaEndPiZeroHomologyEquiv
#print axioms SerrePositivity.KST.Comparison.gammaEndPiZeroHomologyEquiv


-- GammaH0Ring.lean

#check @SerrePositivity.KST.Comparison.gammaEndPinched_vertex
#print axioms SerrePositivity.KST.Comparison.gammaEndPinched_vertex

#check @SerrePositivity.KST.Comparison.gammaEndPiZeroH0Equiv_mk
#print axioms SerrePositivity.KST.Comparison.gammaEndPiZeroH0Equiv_mk

#check @SerrePositivity.KST.Comparison.gammaEndH0RingEquiv
#print axioms SerrePositivity.KST.Comparison.gammaEndH0RingEquiv

#check @SerrePositivity.KST.Comparison.dgAlgebraH0Ring
#print axioms SerrePositivity.KST.Comparison.dgAlgebraH0Ring

#check @SerrePositivity.KST.Comparison.dgAlgebraComponentsH0RingEquiv
#print axioms SerrePositivity.KST.Comparison.dgAlgebraComponentsH0RingEquiv


-- GammaRing.lean

#check @SerrePositivity.KST.Comparison.GammaEnd
#print axioms SerrePositivity.KST.Comparison.GammaEnd

#check @SerrePositivity.KST.Comparison.gammaEndRing
#print axioms SerrePositivity.KST.Comparison.gammaEndRing

#check @SerrePositivity.KST.Comparison.gammaEndPullback
#print axioms SerrePositivity.KST.Comparison.gammaEndPullback

#check @SerrePositivity.KST.Comparison.gammaEndRingObject
#print axioms SerrePositivity.KST.Comparison.gammaEndRingObject

#check @SerrePositivity.KST.Comparison.gammaEnd_underlying
#print axioms SerrePositivity.KST.Comparison.gammaEnd_underlying

#check @SerrePositivity.KST.Comparison.gammaEndDoldKanIso
#print axioms SerrePositivity.KST.Comparison.gammaEndDoldKanIso


-- GammaZeroRing.lean

#check @SerrePositivity.KST.Comparison.standardZeroEval_mul
#print axioms SerrePositivity.KST.Comparison.standardZeroEval_mul

#check @SerrePositivity.KST.Comparison.gammaZeroClosedRingEquiv
#print axioms SerrePositivity.KST.Comparison.gammaZeroClosedRingEquiv


-- GroupCompletion.lean

#check @SerrePositivity.KST.Comparison.bisimplicialBar
#print axioms SerrePositivity.KST.Comparison.bisimplicialBar

#check @SerrePositivity.KST.Comparison.monoidBar
#print axioms SerrePositivity.KST.Comparison.monoidBar

#check @SerrePositivity.KST.Comparison.monoidBarMap
#print axioms SerrePositivity.KST.Comparison.monoidBarMap

#check @SerrePositivity.KST.Comparison.monoidBarMap_id
#print axioms SerrePositivity.KST.Comparison.monoidBarMap_id

#check @SerrePositivity.KST.Comparison.monoidBarMap_comp
#print axioms SerrePositivity.KST.Comparison.monoidBarMap_comp

#check @SerrePositivity.KST.Comparison.monoidBarBasepoint
#print axioms SerrePositivity.KST.Comparison.monoidBarBasepoint

#check @SerrePositivity.KST.Comparison.monoidBarVertexSubsingleton
#print axioms SerrePositivity.KST.Comparison.monoidBarVertexSubsingleton

#check @SerrePositivity.KST.Comparison.monoidBarConnected
#print axioms SerrePositivity.KST.Comparison.monoidBarConnected

#check @SerrePositivity.KST.Comparison.hatGLBar
#print axioms SerrePositivity.KST.Comparison.hatGLBar


-- GroupCompletionBasepoint.lean

#check @SerrePositivity.KST.Comparison.monoidUnitMap
#print axioms SerrePositivity.KST.Comparison.monoidUnitMap

#check @SerrePositivity.KST.Comparison.monoidBarEdgeAt_unit
#print axioms SerrePositivity.KST.Comparison.monoidBarEdgeAt_unit

#check @SerrePositivity.KST.Comparison.monoidBarEdgeMap_unit
#print axioms SerrePositivity.KST.Comparison.monoidBarEdgeMap_unit

#check @SerrePositivity.KST.Comparison.monoidGroupCompletionMap_restriction_ι
#print axioms SerrePositivity.KST.Comparison.monoidGroupCompletionMap_restriction_ι

#check @SerrePositivity.KST.Comparison.monoidGroupCompletionMap_unit
#print axioms SerrePositivity.KST.Comparison.monoidGroupCompletionMap_unit


-- GroupCompletionHomotopy.lean

#check @SerrePositivity.KST.Comparison.monoidPointed
#print axioms SerrePositivity.KST.Comparison.monoidPointed

#check @SerrePositivity.KST.Comparison.exists_groupCompletionKanExtension
#print axioms SerrePositivity.KST.Comparison.exists_groupCompletionKanExtension

#check @SerrePositivity.KST.Comparison.groupCompletionKanMap
#print axioms SerrePositivity.KST.Comparison.groupCompletionKanMap

#check @SerrePositivity.KST.Comparison.groupCompletionKanMap_fac
#print axioms SerrePositivity.KST.Comparison.groupCompletionKanMap_fac

#check @SerrePositivity.KST.Comparison.groupCompletionKanMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.groupCompletionKanMap_localized_isIso

#check @SerrePositivity.KST.Comparison.pointedKanHomotopyEquivOfLocalizedIso
#print axioms SerrePositivity.KST.Comparison.pointedKanHomotopyEquivOfLocalizedIso

#check @SerrePositivity.KST.Comparison.monoidBarHomotopyEquiv
#print axioms SerrePositivity.KST.Comparison.monoidBarHomotopyEquiv


-- GroupCompletionPathIdentity.lean

#check @SerrePositivity.KST.Comparison.monoidGroupCompletionMap_path
#print axioms SerrePositivity.KST.Comparison.monoidGroupCompletionMap_path


-- GroupCompletionSpace.lean

#check @SerrePositivity.KST.Comparison.monoidBarKanPointed
#print axioms SerrePositivity.KST.Comparison.monoidBarKanPointed

#check @SerrePositivity.KST.Comparison.monoidBarKanPointed_kan
#print axioms SerrePositivity.KST.Comparison.monoidBarKanPointed_kan

#check @SerrePositivity.KST.Comparison.monoidGroupCompletionSpace
#print axioms SerrePositivity.KST.Comparison.monoidGroupCompletionSpace

#check @SerrePositivity.KST.Comparison.monoidGroupCompletionSpace_kan
#print axioms SerrePositivity.KST.Comparison.monoidGroupCompletionSpace_kan

#check @SerrePositivity.KST.Comparison.groupCompletionLoopFamily
#print axioms SerrePositivity.KST.Comparison.groupCompletionLoopFamily

#check @SerrePositivity.KST.Comparison.monoidGroupCompletionMap
#print axioms SerrePositivity.KST.Comparison.monoidGroupCompletionMap

#check @SerrePositivity.KST.Comparison.monoidGroupCompletionMap_evaluation
#print axioms SerrePositivity.KST.Comparison.monoidGroupCompletionMap_evaluation


-- GroupCompletionVertexEvaluation.lean

#check @SerrePositivity.KST.Comparison.loopVertex_pullback
#print axioms SerrePositivity.KST.Comparison.loopVertex_pullback

#check @SerrePositivity.KST.Comparison.groupCompletionVertex_simplex_map
#print axioms SerrePositivity.KST.Comparison.groupCompletionVertex_simplex_map


-- GrouplikeColimit.lean

#check @SerrePositivity.KST.Comparison.isGrouplike_of_sequential_isColimit
#print axioms SerrePositivity.KST.Comparison.isGrouplike_of_sequential_isColimit


-- GrouplikeComparison.lean

#check @SerrePositivity.KST.Comparison.monoidGroupCompletionMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.monoidGroupCompletionMap_localized_isIso


-- GrouplikeGL.lean

#check @SerrePositivity.KST.Comparison.hatGL_isGrouplike
#print axioms SerrePositivity.KST.Comparison.hatGL_isGrouplike


-- GrouplikeTranslations.lean

#check @SerrePositivity.KST.Comparison.grouplikeTranslation_localized_isIso
#print axioms SerrePositivity.KST.Comparison.grouplikeTranslation_localized_isIso


-- HatGLCoefficientHomotopy.lean

#check @SerrePositivity.KST.Comparison.hatGLCoefficientHomotopyMulEquiv
#print axioms SerrePositivity.KST.Comparison.hatGLCoefficientHomotopyMulEquiv


-- HatGLCoefficientKan.lean

#check @SerrePositivity.KST.Comparison.simplicialRingHatGLCoefficientHomotopyMulEquiv
#print axioms SerrePositivity.KST.Comparison.simplicialRingHatGLCoefficientHomotopyMulEquiv


-- HatGLCoefficientStabilization.lean

#check @SerrePositivity.KST.Comparison.hatGLCoefficientHomotopy_stabilization
#print axioms SerrePositivity.KST.Comparison.hatGLCoefficientHomotopy_stabilization


-- HatGLComponentIso.lean

#check @SerrePositivity.KST.Comparison.matrixCoefficientEdge
#print axioms SerrePositivity.KST.Comparison.matrixCoefficientEdge

#check @SerrePositivity.KST.Comparison.matrixComponentMap
#print axioms SerrePositivity.KST.Comparison.matrixComponentMap

#check @SerrePositivity.KST.Comparison.matrixComponentMap_simplex
#print axioms SerrePositivity.KST.Comparison.matrixComponentMap_simplex

#check @SerrePositivity.KST.Comparison.hatGLComponentIso
#print axioms SerrePositivity.KST.Comparison.hatGLComponentIso


-- HatGLDelooping.lean

#check @SerrePositivity.KST.Comparison.hatGLGroupCompletionMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.hatGLGroupCompletionMap_localized_isIso

#check @SerrePositivity.KST.Comparison.dgAlgebraHatGLGroupCompletionMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.dgAlgebraHatGLGroupCompletionMap_localized_isIso


-- HatGLPositiveHomotopy.lean

#check @SerrePositivity.KST.Comparison.hatGLMatrixInclusion
#print axioms SerrePositivity.KST.Comparison.hatGLMatrixInclusion

#check @SerrePositivity.KST.Comparison.hatGLSpace_kanComplex
#print axioms SerrePositivity.KST.Comparison.hatGLSpace_kanComplex

#check @SerrePositivity.KST.Comparison.hatGLPositiveHomotopyMulEquiv
#print axioms SerrePositivity.KST.Comparison.hatGLPositiveHomotopyMulEquiv

#check @SerrePositivity.KST.Comparison.hatGLPositiveHomotopyMulEquiv_apply
#print axioms SerrePositivity.KST.Comparison.hatGLPositiveHomotopyMulEquiv_apply


-- HatGLRankCoefficientIso.lean

#check @SerrePositivity.KST.Comparison.nativeHatGLHomotopyGroupDiagram
#print axioms SerrePositivity.KST.Comparison.nativeHatGLHomotopyGroupDiagram

#check @SerrePositivity.KST.Comparison.nativeHatGLHomotopyGroupDiagram_map_succ
#print axioms SerrePositivity.KST.Comparison.nativeHatGLHomotopyGroupDiagram_map_succ

#check @SerrePositivity.KST.Comparison.nativeHatGLRankCoefficientIso
#print axioms SerrePositivity.KST.Comparison.nativeHatGLRankCoefficientIso

#check @SerrePositivity.KST.Comparison.hatGLRankCoefficientIso
#print axioms SerrePositivity.KST.Comparison.hatGLRankCoefficientIso


-- HatGLShiftedEntry.lean

#check @SerrePositivity.KST.Comparison.ringDegenerateVertex_one
#print axioms SerrePositivity.KST.Comparison.ringDegenerateVertex_one

#check @SerrePositivity.KST.Comparison.hatGLShiftedEntryMap
#print axioms SerrePositivity.KST.Comparison.hatGLShiftedEntryMap

#check @SerrePositivity.KST.Comparison.hatGLShiftedEntryMap_basepoint
#print axioms SerrePositivity.KST.Comparison.hatGLShiftedEntryMap_basepoint

#check @SerrePositivity.KST.Comparison.hatGLShiftedEntryMap_app
#print axioms SerrePositivity.KST.Comparison.hatGLShiftedEntryMap_app

#check @SerrePositivity.KST.Comparison.hatGLCoefficientHomotopyMulEquiv_entry
#print axioms SerrePositivity.KST.Comparison.hatGLCoefficientHomotopyMulEquiv_entry


-- HatGLShiftedStabilization.lean

#check @SerrePositivity.KST.Comparison.hatGLSpaceStabilization
#print axioms SerrePositivity.KST.Comparison.hatGLSpaceStabilization

#check @SerrePositivity.KST.Comparison.hatGLSpaceStabilization_unit
#print axioms SerrePositivity.KST.Comparison.hatGLSpaceStabilization_unit

#check @SerrePositivity.KST.Comparison.hatGLShiftedEntryMap_stabilization
#print axioms SerrePositivity.KST.Comparison.hatGLShiftedEntryMap_stabilization


-- HatGLStabilization.lean

#check @SerrePositivity.KST.Comparison.matrixToComponents_stabilization
#print axioms SerrePositivity.KST.Comparison.matrixToComponents_stabilization

#check @SerrePositivity.KST.Comparison.hatGLStabilizationAt
#print axioms SerrePositivity.KST.Comparison.hatGLStabilizationAt

#check @SerrePositivity.KST.Comparison.hatGLStabilization
#print axioms SerrePositivity.KST.Comparison.hatGLStabilization


-- Homology.lean

#check @SerrePositivity.KST.Comparison.freeAbelianSimplicialFunctor
#print axioms SerrePositivity.KST.Comparison.freeAbelianSimplicialFunctor

#check @SerrePositivity.KST.Comparison.unnormalizedIntegralChains
#print axioms SerrePositivity.KST.Comparison.unnormalizedIntegralChains

#check @SerrePositivity.KST.Comparison.normalizedIntegralChains
#print axioms SerrePositivity.KST.Comparison.normalizedIntegralChains

#check @SerrePositivity.KST.Comparison.normalizationInclusion
#print axioms SerrePositivity.KST.Comparison.normalizationInclusion

#check @SerrePositivity.KST.Comparison.normalizationHomotopyEquiv
#print axioms SerrePositivity.KST.Comparison.normalizationHomotopyEquiv

#check @SerrePositivity.KST.Comparison.integralHomologyFunctor
#print axioms SerrePositivity.KST.Comparison.integralHomologyFunctor

#check @SerrePositivity.KST.Comparison.integralHomology
#print axioms SerrePositivity.KST.Comparison.integralHomology

#check @SerrePositivity.KST.Comparison.integralHomologyMap
#print axioms SerrePositivity.KST.Comparison.integralHomologyMap

#check @SerrePositivity.KST.Comparison.unnormalizedIntegralHomologyFunctor
#print axioms SerrePositivity.KST.Comparison.unnormalizedIntegralHomologyFunctor

#check @SerrePositivity.KST.Comparison.normalizationHomologyIso
#print axioms SerrePositivity.KST.Comparison.normalizationHomologyIso

#check @SerrePositivity.KST.Comparison.normalizationHomologyNatIso
#print axioms SerrePositivity.KST.Comparison.normalizationHomologyNatIso


-- HomologyAnodyne.lean

#check @SerrePositivity.KST.Comparison.hornGenerators_le_integralHomology
#print axioms SerrePositivity.KST.Comparison.hornGenerators_le_integralHomology

#check @SerrePositivity.KST.Comparison.hornCellAttachments_le_integralHomology
#print axioms SerrePositivity.KST.Comparison.hornCellAttachments_le_integralHomology

#check @SerrePositivity.KST.Comparison.anodyneExtensions_le_integralHomology
#print axioms SerrePositivity.KST.Comparison.anodyneExtensions_le_integralHomology

#check @SerrePositivity.KST.Comparison.integralHomologyIsomorphism_of_anodyne
#print axioms SerrePositivity.KST.Comparison.integralHomologyIsomorphism_of_anodyne


-- HomologyColimits.lean

#check @SerrePositivity.KST.Comparison.unnormalizedIntegralChainsEvalIso
#print axioms SerrePositivity.KST.Comparison.unnormalizedIntegralChainsEvalIso

#check @SerrePositivity.KST.Comparison.unnormalizedIntegralChains_preservesColimits
#print axioms SerrePositivity.KST.Comparison.unnormalizedIntegralChains_preservesColimits


-- HomologyDegenerate.lean

#check @SerrePositivity.KST.Comparison.integralDegenerateProjection
#print axioms SerrePositivity.KST.Comparison.integralDegenerateProjection

#check @SerrePositivity.KST.Comparison.degenerateIntegralChains
#print axioms SerrePositivity.KST.Comparison.degenerateIntegralChains

#check @SerrePositivity.KST.Comparison.degenerateIntegralChains_split
#print axioms SerrePositivity.KST.Comparison.degenerateIntegralChains_split

#check @SerrePositivity.KST.Comparison.integralDegenerateProjectionNullHomotopy
#print axioms SerrePositivity.KST.Comparison.integralDegenerateProjectionNullHomotopy

#check @SerrePositivity.KST.Comparison.degenerateIntegralChainsContraction
#print axioms SerrePositivity.KST.Comparison.degenerateIntegralChainsContraction

#check @SerrePositivity.KST.Comparison.degenerateIntegralChains_homology_isZero
#print axioms SerrePositivity.KST.Comparison.degenerateIntegralChains_homology_isZero

#check @SerrePositivity.KST.Comparison.integralDegenerateProjection_annihilates_iff
#print axioms SerrePositivity.KST.Comparison.integralDegenerateProjection_annihilates_iff


-- HomologyFilteredColimits.lean

#check @SerrePositivity.KST.Comparison.integralShortComplexFunctor_preservesColimits
#print axioms SerrePositivity.KST.Comparison.integralShortComplexFunctor_preservesColimits

#check @SerrePositivity.KST.Comparison.integralChainHomology_preservesExactColimits
#print axioms SerrePositivity.KST.Comparison.integralChainHomology_preservesExactColimits

#check @SerrePositivity.KST.Comparison.unnormalizedIntegralHomology_preservesExactColimits
#print axioms SerrePositivity.KST.Comparison.unnormalizedIntegralHomology_preservesExactColimits

#check @SerrePositivity.KST.Comparison.integralHomology_preservesExactColimits
#print axioms SerrePositivity.KST.Comparison.integralHomology_preservesExactColimits

#check @SerrePositivity.KST.Comparison.integralHomologyColimitIso
#print axioms SerrePositivity.KST.Comparison.integralHomologyColimitIso

#check @SerrePositivity.KST.Comparison.integralHomologyColimitIso_naturality
#print axioms SerrePositivity.KST.Comparison.integralHomologyColimitIso_naturality

#check @SerrePositivity.KST.Comparison.integralHomologyIsomorphism_colimit
#print axioms SerrePositivity.KST.Comparison.integralHomologyIsomorphism_colimit

#check @SerrePositivity.KST.Comparison.integralHomologyFilteredColimitIso
#print axioms SerrePositivity.KST.Comparison.integralHomologyFilteredColimitIso


-- HomologyHomotopy.lean

#check @SerrePositivity.KST.Comparison.integralHomologyMap_id
#print axioms SerrePositivity.KST.Comparison.integralHomologyMap_id

#check @SerrePositivity.KST.Comparison.integralHomologyMap_comp
#print axioms SerrePositivity.KST.Comparison.integralHomologyMap_comp

#check @SerrePositivity.KST.Comparison.unnormalizedIntegralChainsHomotopy
#print axioms SerrePositivity.KST.Comparison.unnormalizedIntegralChainsHomotopy

#check @SerrePositivity.KST.Comparison.integralHomologyMap_eq_of_homotopy
#print axioms SerrePositivity.KST.Comparison.integralHomologyMap_eq_of_homotopy

#check @SerrePositivity.KST.Comparison.IntegralHomologyIsomorphism
#print axioms SerrePositivity.KST.Comparison.IntegralHomologyIsomorphism

#check @SerrePositivity.KST.Comparison.integralHomologyIsoOfHomotopyInverse
#print axioms SerrePositivity.KST.Comparison.integralHomologyIsoOfHomotopyInverse


-- HomologyHorn.lean

#check @SerrePositivity.KST.Comparison.hornIntegralHomologyIso
#print axioms SerrePositivity.KST.Comparison.hornIntegralHomologyIso

#check @SerrePositivity.KST.Comparison.horn_integralHomologyIsomorphism
#print axioms SerrePositivity.KST.Comparison.horn_integralHomologyIsomorphism


-- HomologyKanReplacement.lean

#check @SerrePositivity.KST.Comparison.kanReplacementUnit_integralHomologyIsomorphism
#print axioms SerrePositivity.KST.Comparison.kanReplacementUnit_integralHomologyIsomorphism

#check @SerrePositivity.KST.Comparison.integralHomologyIsomorphism_of_localized_isIso
#print axioms SerrePositivity.KST.Comparison.integralHomologyIsomorphism_of_localized_isIso

#check @SerrePositivity.KST.Comparison.monoidGroupCompletionMap_integralHomologyIsomorphism
#print axioms SerrePositivity.KST.Comparison.monoidGroupCompletionMap_integralHomologyIsomorphism


-- HomologyMorphismProperty.lean

#check @SerrePositivity.KST.Comparison.integralHomologyEquivalences
#print axioms SerrePositivity.KST.Comparison.integralHomologyEquivalences

#check @SerrePositivity.KST.Comparison.integralHomologyEquivalences_iff
#print axioms SerrePositivity.KST.Comparison.integralHomologyEquivalences_iff

#check @SerrePositivity.KST.Comparison.integralHomologyEquivalences_isMultiplicative
#print axioms SerrePositivity.KST.Comparison.integralHomologyEquivalences_isMultiplicative

#check @SerrePositivity.KST.Comparison.integralHomologyEquivalences_respectsIso
#print axioms SerrePositivity.KST.Comparison.integralHomologyEquivalences_respectsIso

#check @SerrePositivity.KST.Comparison.integralHomologyEquivalences_stableRetracts
#print axioms SerrePositivity.KST.Comparison.integralHomologyEquivalences_stableRetracts

#check @SerrePositivity.KST.Comparison.integralHomologyEquivalences_stableColimits
#print axioms SerrePositivity.KST.Comparison.integralHomologyEquivalences_stableColimits

#check @SerrePositivity.KST.Comparison.integralHomology_preservesCoproductsOfShape
#print axioms SerrePositivity.KST.Comparison.integralHomology_preservesCoproductsOfShape

#check @SerrePositivity.KST.Comparison.integralHomologyEquivalences_stableCoproducts
#print axioms SerrePositivity.KST.Comparison.integralHomologyEquivalences_stableCoproducts

#check @SerrePositivity.KST.Comparison.integralHomologyEquivalences_stableFilteredColimits
#print axioms SerrePositivity.KST.Comparison.integralHomologyEquivalences_stableFilteredColimits


-- HomologyPairContraction.lean

#check @SerrePositivity.KST.Comparison.integralHomologyMap_endpoints_eq
#print axioms SerrePositivity.KST.Comparison.integralHomologyMap_endpoints_eq

#check @SerrePositivity.KST.Comparison.integralHomologyIsoOfPairContraction
#print axioms SerrePositivity.KST.Comparison.integralHomologyIsoOfPairContraction


-- HomologyPointwise.lean

#check @SerrePositivity.KST.Comparison.shortComplexPointwiseHomologyIso
#print axioms SerrePositivity.KST.Comparison.shortComplexPointwiseHomologyIso

#check @SerrePositivity.KST.Comparison.shortComplexColimitCocone
#print axioms SerrePositivity.KST.Comparison.shortComplexColimitCocone

#check @SerrePositivity.KST.Comparison.shortComplexColimitIsColimit
#print axioms SerrePositivity.KST.Comparison.shortComplexColimitIsColimit

#check @SerrePositivity.KST.Comparison.shortComplexExactColimitHomologyIso
#print axioms SerrePositivity.KST.Comparison.shortComplexExactColimitHomologyIso

#check @SerrePositivity.KST.Comparison.shortComplexExactColimitHomologyIso_ι
#print axioms SerrePositivity.KST.Comparison.shortComplexExactColimitHomologyIso_ι

#check @SerrePositivity.KST.Comparison.shortComplexHomologyColimitIsColimit
#print axioms SerrePositivity.KST.Comparison.shortComplexHomologyColimitIsColimit

#check @SerrePositivity.KST.Comparison.shortComplexHomology_preservesExactColimits
#print axioms SerrePositivity.KST.Comparison.shortComplexHomology_preservesExactColimits


-- HomologyPushout.lean

#check @SerrePositivity.KST.Comparison.integralChainCokernelSequence_shortExact
#print axioms SerrePositivity.KST.Comparison.integralChainCokernelSequence_shortExact

#check @SerrePositivity.KST.Comparison.integralChain_quasiIso_iff_cokernel_acyclic
#print axioms SerrePositivity.KST.Comparison.integralChain_quasiIso_iff_cokernel_acyclic

#check @SerrePositivity.KST.Comparison.integralChain_quasiIso_of_pushout
#print axioms SerrePositivity.KST.Comparison.integralChain_quasiIso_of_pushout

#check @SerrePositivity.KST.Comparison.integralHomologyIsomorphism_of_pushout
#print axioms SerrePositivity.KST.Comparison.integralHomologyIsomorphism_of_pushout


-- HomologyQuasiIso.lean

#check @SerrePositivity.KST.Comparison.integralHomologyIsomorphism_iff_normalized_quasiIso
#print axioms SerrePositivity.KST.Comparison.integralHomologyIsomorphism_iff_normalized_quasiIso

#check @SerrePositivity.KST.Comparison.normalizationInclusion_quasiIso
#print axioms SerrePositivity.KST.Comparison.normalizationInclusion_quasiIso

#check @SerrePositivity.KST.Comparison.integralHomologyIsomorphism_iff_unnormalized_quasiIso
#print axioms SerrePositivity.KST.Comparison.integralHomologyIsomorphism_iff_unnormalized_quasiIso


-- HomologyRelative.lean

#check @SerrePositivity.KST.Comparison.unnormalizedIntegralChains_map_mono
#print axioms SerrePositivity.KST.Comparison.unnormalizedIntegralChains_map_mono

#check @SerrePositivity.KST.Comparison.normalizedIntegralChains_map_mono
#print axioms SerrePositivity.KST.Comparison.normalizedIntegralChains_map_mono

#check @SerrePositivity.KST.Comparison.relativeIntegralChains
#print axioms SerrePositivity.KST.Comparison.relativeIntegralChains

#check @SerrePositivity.KST.Comparison.relativeIntegralChainsMap
#print axioms SerrePositivity.KST.Comparison.relativeIntegralChainsMap

#check @SerrePositivity.KST.Comparison.relativeIntegralChainsFunctor
#print axioms SerrePositivity.KST.Comparison.relativeIntegralChainsFunctor

#check @SerrePositivity.KST.Comparison.relativeIntegralHomologyFunctor
#print axioms SerrePositivity.KST.Comparison.relativeIntegralHomologyFunctor

#check @SerrePositivity.KST.Comparison.relativeIntegralHomology
#print axioms SerrePositivity.KST.Comparison.relativeIntegralHomology

#check @SerrePositivity.KST.Comparison.relativeIntegralChainsSequence
#print axioms SerrePositivity.KST.Comparison.relativeIntegralChainsSequence

#check @SerrePositivity.KST.Comparison.relativeIntegralChainsSequence_shortExact
#print axioms SerrePositivity.KST.Comparison.relativeIntegralChainsSequence_shortExact

#check @SerrePositivity.KST.Comparison.relativeIntegralHomologyBoundary
#print axioms SerrePositivity.KST.Comparison.relativeIntegralHomologyBoundary

#check @SerrePositivity.KST.Comparison.relativeIntegralHomology_comp_boundary
#print axioms SerrePositivity.KST.Comparison.relativeIntegralHomology_comp_boundary

#check @SerrePositivity.KST.Comparison.relativeIntegralHomology_boundary_comp
#print axioms SerrePositivity.KST.Comparison.relativeIntegralHomology_boundary_comp

#check @SerrePositivity.KST.Comparison.relativeIntegralHomology_exact_at_source
#print axioms SerrePositivity.KST.Comparison.relativeIntegralHomology_exact_at_source

#check @SerrePositivity.KST.Comparison.relativeIntegralHomology_exact_at_target
#print axioms SerrePositivity.KST.Comparison.relativeIntegralHomology_exact_at_target

#check @SerrePositivity.KST.Comparison.relativeIntegralHomology_exact_at_relative
#print axioms SerrePositivity.KST.Comparison.relativeIntegralHomology_exact_at_relative


-- HomotopyPullback.lean

#check @SerrePositivity.KST.Comparison.homotopyPullbackObject
#print axioms SerrePositivity.KST.Comparison.homotopyPullbackObject

#check @SerrePositivity.KST.Comparison.homotopyPullbackProjection_fibration
#print axioms SerrePositivity.KST.Comparison.homotopyPullbackProjection_fibration

#check @SerrePositivity.KST.Comparison.homotopyPullbackObject_kan
#print axioms SerrePositivity.KST.Comparison.homotopyPullbackObject_kan

#check @SerrePositivity.KST.Comparison.homotopyPullbackComparison
#print axioms SerrePositivity.KST.Comparison.homotopyPullbackComparison

#check @SerrePositivity.KST.Comparison.homotopyPullbackComparison_fst
#print axioms SerrePositivity.KST.Comparison.homotopyPullbackComparison_fst

#check @SerrePositivity.KST.Comparison.homotopyPullbackComparison_snd
#print axioms SerrePositivity.KST.Comparison.homotopyPullbackComparison_snd

#check @SerrePositivity.KST.Comparison.homotopyPullbackMap
#print axioms SerrePositivity.KST.Comparison.homotopyPullbackMap

#check @SerrePositivity.KST.Comparison.IsHomotopyPullback
#print axioms SerrePositivity.KST.Comparison.IsHomotopyPullback


-- HomotopyPullbackGeneralPasting.lean

#check @SerrePositivity.KST.Comparison.isHomotopyPullback_paste_horiz
#print axioms SerrePositivity.KST.Comparison.isHomotopyPullback_paste_horiz


-- HomotopyPullbackInvariance.lean

#check @SerrePositivity.KST.Comparison.homotopyPullbackMap_fst
#print axioms SerrePositivity.KST.Comparison.homotopyPullbackMap_fst

#check @SerrePositivity.KST.Comparison.homotopyPullbackMap_snd
#print axioms SerrePositivity.KST.Comparison.homotopyPullbackMap_snd

#check @SerrePositivity.KST.Comparison.homotopyPullbackMap_localized_isIso_fixed_base
#print axioms SerrePositivity.KST.Comparison.homotopyPullbackMap_localized_isIso_fixed_base

#check @SerrePositivity.KST.Comparison.homotopyPullbackMap_localized_isIso_fixed_kan_base
#print axioms SerrePositivity.KST.Comparison.homotopyPullbackMap_localized_isIso_fixed_kan_base


-- HomotopyPullbackPasting.lean

#check @SerrePositivity.KST.Comparison.isHomotopyPullback_paste_horiz_of_middle_fibration
#print axioms SerrePositivity.KST.Comparison.isHomotopyPullback_paste_horiz_of_middle_fibration


-- HomotopyPullbackSymmetry.lean

#check @SerrePositivity.KST.Comparison.isHomotopyPullback_flip_iff
#print axioms SerrePositivity.KST.Comparison.isHomotopyPullback_flip_iff

#check @SerrePositivity.KST.Comparison.isHomotopyPullback_of_left_fibration
#print axioms SerrePositivity.KST.Comparison.isHomotopyPullback_of_left_fibration


-- HomotopyPullbackThreeInputs.lean

#check @SerrePositivity.KST.Comparison.homotopyPullbackMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.homotopyPullbackMap_localized_isIso

#check @SerrePositivity.KST.Comparison.homotopyPullbackComparison_naturality
#print axioms SerrePositivity.KST.Comparison.homotopyPullbackComparison_naturality

#check @SerrePositivity.KST.Comparison.isHomotopyPullback_iff_of_localized_isIso
#print axioms SerrePositivity.KST.Comparison.isHomotopyPullback_iff_of_localized_isIso


-- HornChainBoundary.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainVertex_map_hornFaces
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainVertex_map_hornFaces

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainToHorn_boundary
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainToHorn_boundary


-- HornChainMissingVertex.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainVertex_common_missing
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainVertex_common_missing


-- HornChainNerve.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainToSimplex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainToSimplex

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainToSimplex_range_le
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainToSimplex_range_le

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainToHorn
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainToHorn


-- HornChainVertices.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornFaceSet
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornFaceSet

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceSet_of_le
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceSet_of_le

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceChoice
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceChoice

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainVertex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainVertex

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainVertex_exists_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainVertex_exists_face

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainVertex_of_all_faces
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornChainVertex_of_all_faces


-- HornContraction.lean

#check @SerrePositivity.KST.Comparison.simplexOrderMap
#print axioms SerrePositivity.KST.Comparison.simplexOrderMap

#check @SerrePositivity.KST.Comparison.simplexOrderHomotopyMap
#print axioms SerrePositivity.KST.Comparison.simplexOrderHomotopyMap

#check @SerrePositivity.KST.Comparison.simplexOrderHomotopy
#print axioms SerrePositivity.KST.Comparison.simplexOrderHomotopy

#check @SerrePositivity.KST.Comparison.vertexMeet
#print axioms SerrePositivity.KST.Comparison.vertexMeet

#check @SerrePositivity.KST.Comparison.simplexOrderHomotopyMap_mem_horn
#print axioms SerrePositivity.KST.Comparison.simplexOrderHomotopyMap_mem_horn

#check @SerrePositivity.KST.Comparison.simplexMeetToIdentity
#print axioms SerrePositivity.KST.Comparison.simplexMeetToIdentity

#check @SerrePositivity.KST.Comparison.simplexMeetToVertex
#print axioms SerrePositivity.KST.Comparison.simplexMeetToVertex

#check @SerrePositivity.KST.Comparison.simplexMeetToIdentity_mem_horn
#print axioms SerrePositivity.KST.Comparison.simplexMeetToIdentity_mem_horn

#check @SerrePositivity.KST.Comparison.simplexMeetToVertex_mem_horn
#print axioms SerrePositivity.KST.Comparison.simplexMeetToVertex_mem_horn


-- HornFaceInclusionAnodyne.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceAddVertex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceAddVertex

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceAddVertex_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceAddVertex_mem

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceSingleton_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceSingleton_mem

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceInclusion_anodyne
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceInclusion_anodyne


-- HornFaceNerveCover.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceNerve_missingVertex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceNerve_missingVertex

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceNerve_faceCover
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceNerve_faceCover


-- HornFacePoset.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornFacePoset
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornFacePoset

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFacePoset_partialOrder
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFacePoset_partialOrder

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceInclusion
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceInclusion

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFacesToSimplex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFacesToSimplex

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFacesToSimplex_range_le
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFacesToSimplex_range_le

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFacesLastVertex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFacesLastVertex


-- HornPreimage.lean

#check @SerrePositivity.KST.Comparison.const_horn_vertex_mem
#print axioms SerrePositivity.KST.Comparison.const_horn_vertex_mem

#check @SerrePositivity.KST.Comparison.horn_preimage_anodyne
#print axioms SerrePositivity.KST.Comparison.horn_preimage_anodyne

#check @SerrePositivity.KST.Comparison.horn_preimage_localized_isIso
#print axioms SerrePositivity.KST.Comparison.horn_preimage_localized_isIso

#check @SerrePositivity.KST.Comparison.subcomplexPreimage_isPullback
#print axioms SerrePositivity.KST.Comparison.subcomplexPreimage_isPullback

#check @SerrePositivity.KST.Comparison.pullback_horn_localized_isIso
#print axioms SerrePositivity.KST.Comparison.pullback_horn_localized_isIso

#check @SerrePositivity.KST.Comparison.pullback_horn_anodyne
#print axioms SerrePositivity.KST.Comparison.pullback_horn_anodyne


-- HornRightColimit.lean

#check @SerrePositivity.KST.Comparison.hornRight_filteredColimit
#print axioms SerrePositivity.KST.Comparison.hornRight_filteredColimit

#check @SerrePositivity.KST.Comparison.hornRight_sequentialColimit
#print axioms SerrePositivity.KST.Comparison.hornRight_sequentialColimit


-- HornSimplexFaceFactorization.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSimplexFaceFactorization
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSimplexFaceFactorization

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionFaceCover
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionFaceCover


-- HornSubdivisionComparison.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSimplexOrderHom
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSimplexOrderHom

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSimplexOrderHom_map_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSimplexOrderHom_map_mem

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSimplexFaceMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSimplexFaceMap

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFacesExUnit
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFacesExUnit

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison


-- HornSubdivisionFaceMaps.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionFaceMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionFaceMap

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionFaceMap_ambient
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionFaceMap_ambient

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionNerveFaceCover
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionNerveFaceCover

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionFaceMap_common
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionFaceMap_common


-- HornSubdivisionInclusion.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSimplex_yoneda_inclusion
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSimplex_yoneda_inclusion

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_inclusion
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_inclusion


-- HornSubdivisionIso.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_app_injective
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_app_injective

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_isIso
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_isIso


-- HornSubdivisionLastVertex.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFacesExUnit_lastVertex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFacesExUnit_lastVertex

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_lastVertex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_lastVertex


-- HornSubdivisionSurjective.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceInclusion_nerve_app_injective
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornFaceInclusion_nerve_app_injective

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_face

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_app_surjective
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_app_surjective

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_epi
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.hornSubdivisionComparison_epi


-- IntegerCoefficientComparison.lean

#check @SerrePositivity.KST.Comparison.integerCoefficientUnit
#print axioms SerrePositivity.KST.Comparison.integerCoefficientUnit

#check @SerrePositivity.KST.Comparison.integerCoefficientComparison
#print axioms SerrePositivity.KST.Comparison.integerCoefficientComparison

#check @SerrePositivity.KST.Comparison.integerCoefficientComparison_unit
#print axioms SerrePositivity.KST.Comparison.integerCoefficientComparison_unit

#check @SerrePositivity.KST.Comparison.integerCoefficientObjIso
#print axioms SerrePositivity.KST.Comparison.integerCoefficientObjIso

#check @SerrePositivity.KST.Comparison.integerCoefficientComparison_app
#print axioms SerrePositivity.KST.Comparison.integerCoefficientComparison_app

#check @SerrePositivity.KST.Comparison.integerCoefficientSimplicialIso
#print axioms SerrePositivity.KST.Comparison.integerCoefficientSimplicialIso

#check @SerrePositivity.KST.Comparison.integerLocalCoefficientChainsIso
#print axioms SerrePositivity.KST.Comparison.integerLocalCoefficientChainsIso

#check @SerrePositivity.KST.Comparison.integerLocalCoefficientHomologyIso
#print axioms SerrePositivity.KST.Comparison.integerLocalCoefficientHomologyIso


-- IntegerCoefficientGroup.lean

#check @SerrePositivity.KST.Comparison.integerCoefficientGroup
#print axioms SerrePositivity.KST.Comparison.integerCoefficientGroup

#check @SerrePositivity.KST.Comparison.integerCoefficientGroupEquiv
#print axioms SerrePositivity.KST.Comparison.integerCoefficientGroupEquiv

#check @SerrePositivity.KST.Comparison.integerGeneratorMap
#print axioms SerrePositivity.KST.Comparison.integerGeneratorMap

#check @SerrePositivity.KST.Comparison.integerCoefficientCoproductIso
#print axioms SerrePositivity.KST.Comparison.integerCoefficientCoproductIso


-- IntegerCoefficientNaturality.lean

#check @SerrePositivity.KST.Comparison.localCoefficientSimplicialMap_unit
#print axioms SerrePositivity.KST.Comparison.localCoefficientSimplicialMap_unit

#check @SerrePositivity.KST.Comparison.integerCoefficientComparison_naturality
#print axioms SerrePositivity.KST.Comparison.integerCoefficientComparison_naturality

#check @SerrePositivity.KST.Comparison.integerLocalCoefficientChainsIso_naturality
#print axioms SerrePositivity.KST.Comparison.integerLocalCoefficientChainsIso_naturality

#check @SerrePositivity.KST.Comparison.integerLocalCoefficientHomologyIso_naturality
#print axioms SerrePositivity.KST.Comparison.integerLocalCoefficientHomologyIso_naturality

#check @SerrePositivity.KST.Comparison.integralHomologyIsomorphism_of_local
#print axioms SerrePositivity.KST.Comparison.integralHomologyIsomorphism_of_local


-- IntervalBoundaryFamily.lean

#check @SerrePositivity.KST.Comparison.intervalBoundaryTensorIsColimit
#print axioms SerrePositivity.KST.Comparison.intervalBoundaryTensorIsColimit

#check @SerrePositivity.KST.Comparison.intervalBoundaryMap
#print axioms SerrePositivity.KST.Comparison.intervalBoundaryMap

#check @SerrePositivity.KST.Comparison.intervalBoundaryMap_zero
#print axioms SerrePositivity.KST.Comparison.intervalBoundaryMap_zero

#check @SerrePositivity.KST.Comparison.intervalBoundaryMap_one
#print axioms SerrePositivity.KST.Comparison.intervalBoundaryMap_one

#check @SerrePositivity.KST.Comparison.intervalBoundaryMap_precomp
#print axioms SerrePositivity.KST.Comparison.intervalBoundaryMap_precomp

#check @SerrePositivity.KST.Comparison.intervalBoundaryMap_postcomp
#print axioms SerrePositivity.KST.Comparison.intervalBoundaryMap_postcomp

#check @SerrePositivity.KST.Comparison.intervalBoundaryMap_self
#print axioms SerrePositivity.KST.Comparison.intervalBoundaryMap_self


-- KanAnodyneBaseChange.lean

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_horn_anodyne
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_horn_anodyne

#check @SerrePositivity.KST.Comparison.sliceFiberRightAdjoint_rlp
#print axioms SerrePositivity.KST.Comparison.sliceFiberRightAdjoint_rlp

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_anodyne
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_anodyne

#check @SerrePositivity.KST.Comparison.pullback_anodyne
#print axioms SerrePositivity.KST.Comparison.pullback_anodyne

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_horn_localized_isIso
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_horn_localized_isIso

#check @SerrePositivity.KST.Comparison.sliceFiberRightAdjoint_test_rlp
#print axioms SerrePositivity.KST.Comparison.sliceFiberRightAdjoint_test_rlp

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_anodyne_localized_isIso
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_anodyne_localized_isIso

#check @SerrePositivity.KST.Comparison.pullback_anodyne_localized_isIso
#print axioms SerrePositivity.KST.Comparison.pullback_anodyne_localized_isIso


-- KanBarRows.lean

#check @SerrePositivity.KST.Comparison.monoidBarRow_kanComplex
#print axioms SerrePositivity.KST.Comparison.monoidBarRow_kanComplex

#check @SerrePositivity.KST.Comparison.actionBarProjection_row_rlp
#print axioms SerrePositivity.KST.Comparison.actionBarProjection_row_rlp

#check @SerrePositivity.KST.Comparison.regularBarRow_kanComplex
#print axioms SerrePositivity.KST.Comparison.regularBarRow_kanComplex


-- KanBasePullback.lean

#check @SerrePositivity.KST.Comparison.sliceFiberRightAdjoint_kan
#print axioms SerrePositivity.KST.Comparison.sliceFiberRightAdjoint_kan

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_localizedMono_isIso
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_localizedMono_isIso

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_localized_isIso
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_localized_isIso

#check @SerrePositivity.KST.Comparison.pullback_localized_isIso_of_kan_base
#print axioms SerrePositivity.KST.Comparison.pullback_localized_isIso_of_kan_base


-- KanBaseSpanGluing.lean

#check @SerrePositivity.KST.Comparison.spanCylinder_vertex_homotopyPullback_of_kan_base
#print axioms SerrePositivity.KST.Comparison.spanCylinder_vertex_homotopyPullback_of_kan_base


-- KanReplacementSquares.lean

#check @SerrePositivity.KST.Comparison.naturalitySquare
#print axioms SerrePositivity.KST.Comparison.naturalitySquare

#check @SerrePositivity.KST.Comparison.naturalitySquare_factorization_iff
#print axioms SerrePositivity.KST.Comparison.naturalitySquare_factorization_iff

#check @SerrePositivity.KST.Comparison.diagramArrow
#print axioms SerrePositivity.KST.Comparison.diagramArrow

#check @SerrePositivity.KST.Comparison.diagramKan_arrowSquare_iff
#print axioms SerrePositivity.KST.Comparison.diagramKan_arrowSquare_iff

#check @SerrePositivity.KST.Comparison.spanCylinderKanUnit_localized_isIso
#print axioms SerrePositivity.KST.Comparison.spanCylinderKanUnit_localized_isIso

#check @SerrePositivity.KST.Comparison.spanCylinderKan_vertexSquare_iff
#print axioms SerrePositivity.KST.Comparison.spanCylinderKan_vertexSquare_iff


-- KanSquareReplacement.lean

#check @SerrePositivity.KST.Comparison.kanSquareTop
#print axioms SerrePositivity.KST.Comparison.kanSquareTop

#check @SerrePositivity.KST.Comparison.kanReplacementSquare
#print axioms SerrePositivity.KST.Comparison.kanReplacementSquare

#check @SerrePositivity.KST.Comparison.kanSquareTop_unit
#print axioms SerrePositivity.KST.Comparison.kanSquareTop_unit

#check @SerrePositivity.KST.Comparison.kanReplacementSquare_homotopyPullback_iff
#print axioms SerrePositivity.KST.Comparison.kanReplacementSquare_homotopyPullback_iff


-- LocalCoefficientAnodyne.lean

#check @SerrePositivity.KST.Comparison.overHornMap_quasiIso
#print axioms SerrePositivity.KST.Comparison.overHornMap_quasiIso

#check @SerrePositivity.KST.Comparison.overHornGenerators_le_localHomology
#print axioms SerrePositivity.KST.Comparison.overHornGenerators_le_localHomology

#check @SerrePositivity.KST.Comparison.overHornGenerators_le_underlyingMonomorphisms
#print axioms SerrePositivity.KST.Comparison.overHornGenerators_le_underlyingMonomorphisms

#check @SerrePositivity.KST.Comparison.overHornCellAttachments_le_localHomology
#print axioms SerrePositivity.KST.Comparison.overHornCellAttachments_le_localHomology

#check @SerrePositivity.KST.Comparison.overLocalHomologyEquivalence_of_anodyne
#print axioms SerrePositivity.KST.Comparison.overLocalHomologyEquivalence_of_anodyne

#check @SerrePositivity.KST.Comparison.localHomologyIsomorphism_of_anodyne
#print axioms SerrePositivity.KST.Comparison.localHomologyIsomorphism_of_anodyne


-- LocalCoefficientColimits.lean

#check @SerrePositivity.KST.Comparison.overSimplicialEvaluation_preservesColimits
#print axioms SerrePositivity.KST.Comparison.overSimplicialEvaluation_preservesColimits

#check @SerrePositivity.KST.Comparison.overSimplicialEvaluation_preservesMonomorphisms
#print axioms SerrePositivity.KST.Comparison.overSimplicialEvaluation_preservesMonomorphisms

#check @SerrePositivity.KST.Comparison.overLocalCoefficientSimplicialFunctor_preservesColimits
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientSimplicialFunctor_preservesColimits

#check @SerrePositivity.KST.Comparison.overLocalCoefficientSimplicialFunctor_preservesMonomorphisms
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientSimplicialFunctor_preservesMonomorphisms

#check @SerrePositivity.KST.Comparison.normalizedMooreComplexAb_isEquivalence
#print axioms SerrePositivity.KST.Comparison.normalizedMooreComplexAb_isEquivalence

#check @SerrePositivity.KST.Comparison.overLocalCoefficientChainsFunctor_preservesColimits
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientChainsFunctor_preservesColimits

#check @SerrePositivity.KST.Comparison.overLocalCoefficientChainsFunctor_preservesMonomorphisms
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientChainsFunctor_preservesMonomorphisms


-- LocalCoefficientDegreeComparison.lean

#check @SerrePositivity.KST.Comparison.overSimplicialEvaluation
#print axioms SerrePositivity.KST.Comparison.overSimplicialEvaluation

#check @SerrePositivity.KST.Comparison.overSimplexCoefficientFamily
#print axioms SerrePositivity.KST.Comparison.overSimplexCoefficientFamily

#check @SerrePositivity.KST.Comparison.coefficientSimplicialObjIsoSigma_inv_ι
#print axioms SerrePositivity.KST.Comparison.coefficientSimplicialObjIsoSigma_inv_ι

#check @SerrePositivity.KST.Comparison.overLocalCoefficientSourceIso_app
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientSourceIso_app

#check @SerrePositivity.KST.Comparison.overLocalCoefficientDegreeIso
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientDegreeIso


-- LocalCoefficientFibers.lean

#check @SerrePositivity.KST.Comparison.coefficientFiberFamily
#print axioms SerrePositivity.KST.Comparison.coefficientFiberFamily

#check @SerrePositivity.KST.Comparison.coefficientFiberEndpoint
#print axioms SerrePositivity.KST.Comparison.coefficientFiberEndpoint

#check @SerrePositivity.KST.Comparison.coefficientFiberTransport
#print axioms SerrePositivity.KST.Comparison.coefficientFiberTransport

#check @SerrePositivity.KST.Comparison.coefficientFiberEndpoint_eq
#print axioms SerrePositivity.KST.Comparison.coefficientFiberEndpoint_eq

#check @SerrePositivity.KST.Comparison.coefficientFiberCocone
#print axioms SerrePositivity.KST.Comparison.coefficientFiberCocone

#check @SerrePositivity.KST.Comparison.coefficientFiberIdentity
#print axioms SerrePositivity.KST.Comparison.coefficientFiberIdentity

#check @SerrePositivity.KST.Comparison.coefficientFiberCocone_identity
#print axioms SerrePositivity.KST.Comparison.coefficientFiberCocone_identity

#check @SerrePositivity.KST.Comparison.coefficientFiberIsColimit
#print axioms SerrePositivity.KST.Comparison.coefficientFiberIsColimit

#check @SerrePositivity.KST.Comparison.coefficientSimplicialObjIsoSigma
#print axioms SerrePositivity.KST.Comparison.coefficientSimplicialObjIsoSigma

#check @SerrePositivity.KST.Comparison.coefficientSimplicialObjIsoSigma_unit
#print axioms SerrePositivity.KST.Comparison.coefficientSimplicialObjIsoSigma_unit


-- LocalCoefficientFunctoriality.lean

#check @SerrePositivity.KST.Comparison.localCoefficientSimplicialMap_id
#print axioms SerrePositivity.KST.Comparison.localCoefficientSimplicialMap_id

#check @SerrePositivity.KST.Comparison.localCoefficientSimplicialMap_comp
#print axioms SerrePositivity.KST.Comparison.localCoefficientSimplicialMap_comp

#check @SerrePositivity.KST.Comparison.localCoefficientChainsMap_id
#print axioms SerrePositivity.KST.Comparison.localCoefficientChainsMap_id

#check @SerrePositivity.KST.Comparison.localCoefficientChainsMap_comp
#print axioms SerrePositivity.KST.Comparison.localCoefficientChainsMap_comp


-- LocalCoefficientHorn.lean

#check @SerrePositivity.KST.Comparison.localCoefficientChainsMapArrowIso
#print axioms SerrePositivity.KST.Comparison.localCoefficientChainsMapArrowIso

#check @SerrePositivity.KST.Comparison.localCoefficientHorn_quasiIso
#print axioms SerrePositivity.KST.Comparison.localCoefficientHorn_quasiIso

#check @SerrePositivity.KST.Comparison.horn_localHomologyIsomorphism
#print axioms SerrePositivity.KST.Comparison.horn_localHomologyIsomorphism


-- LocalCoefficientKanReplacement.lean

#check @SerrePositivity.KST.Comparison.kanReplacementUnit_localHomologyIsomorphism
#print axioms SerrePositivity.KST.Comparison.kanReplacementUnit_localHomologyIsomorphism


-- LocalCoefficientMorphismProperty.lean

#check @SerrePositivity.KST.Comparison.overLocalHomologyFunctor
#print axioms SerrePositivity.KST.Comparison.overLocalHomologyFunctor

#check @SerrePositivity.KST.Comparison.overLocalHomologyEquivalences
#print axioms SerrePositivity.KST.Comparison.overLocalHomologyEquivalences

#check @SerrePositivity.KST.Comparison.overLocalHomologyEquivalences_iff
#print axioms SerrePositivity.KST.Comparison.overLocalHomologyEquivalences_iff

#check @SerrePositivity.KST.Comparison.overLocalHomologyEquivalences_isMultiplicative
#print axioms SerrePositivity.KST.Comparison.overLocalHomologyEquivalences_isMultiplicative

#check @SerrePositivity.KST.Comparison.overLocalHomologyEquivalences_respectsIso
#print axioms SerrePositivity.KST.Comparison.overLocalHomologyEquivalences_respectsIso

#check @SerrePositivity.KST.Comparison.overLocalHomologyEquivalences_stableRetracts
#print axioms SerrePositivity.KST.Comparison.overLocalHomologyEquivalences_stableRetracts

#check @SerrePositivity.KST.Comparison.overLocalHomology_preservesExactColimits
#print axioms SerrePositivity.KST.Comparison.overLocalHomology_preservesExactColimits

#check @SerrePositivity.KST.Comparison.overLocalHomologyEquivalences_stableColimits
#print axioms SerrePositivity.KST.Comparison.overLocalHomologyEquivalences_stableColimits

#check @SerrePositivity.KST.Comparison.overLocalHomologyEquivalences_stableCoproducts
#print axioms SerrePositivity.KST.Comparison.overLocalHomologyEquivalences_stableCoproducts

#check @SerrePositivity.KST.Comparison.overLocalHomologyEquivalences_stableFilteredColimits
#print axioms SerrePositivity.KST.Comparison.overLocalHomologyEquivalences_stableFilteredColimits

#check @SerrePositivity.KST.Comparison.overUnderlyingMonomorphisms
#print axioms SerrePositivity.KST.Comparison.overUnderlyingMonomorphisms

#check @SerrePositivity.KST.Comparison.overUnderlyingMonomorphisms_stableCoproducts
#print axioms SerrePositivity.KST.Comparison.overUnderlyingMonomorphisms_stableCoproducts


-- LocalCoefficientNaturality.lean

#check @SerrePositivity.KST.Comparison.coefficientSimplicialFunctor_map_unit
#print axioms SerrePositivity.KST.Comparison.coefficientSimplicialFunctor_map_unit

#check @SerrePositivity.KST.Comparison.localCoefficientSimplicialMap_naturality
#print axioms SerrePositivity.KST.Comparison.localCoefficientSimplicialMap_naturality

#check @SerrePositivity.KST.Comparison.localCoefficientChainsMap_naturality
#print axioms SerrePositivity.KST.Comparison.localCoefficientChainsMap_naturality


-- LocalCoefficientOverFunctor.lean

#check @SerrePositivity.KST.Comparison.overLocalCoefficientSimplicialMap_id
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientSimplicialMap_id

#check @SerrePositivity.KST.Comparison.overLocalCoefficientSimplicialMap_comp
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientSimplicialMap_comp

#check @SerrePositivity.KST.Comparison.overLocalCoefficientSimplicialFunctor
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientSimplicialFunctor

#check @SerrePositivity.KST.Comparison.overLocalCoefficientChainsFunctor
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientChainsFunctor

#check @SerrePositivity.KST.Comparison.overLocalCoefficientUnnormalizedChainsFunctor
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientUnnormalizedChainsFunctor


-- LocalCoefficientTrivialization.lean

#check @SerrePositivity.KST.Comparison.localCoefficientConstIsoOfInitial
#print axioms SerrePositivity.KST.Comparison.localCoefficientConstIsoOfInitial

#check @SerrePositivity.KST.Comparison.standardSimplexRepresentableBy
#print axioms SerrePositivity.KST.Comparison.standardSimplexRepresentableBy

#check @SerrePositivity.KST.Comparison.standardSimplexIdentityElement
#print axioms SerrePositivity.KST.Comparison.standardSimplexIdentityElement

#check @SerrePositivity.KST.Comparison.standardSimplexIdentityElementIsInitial
#print axioms SerrePositivity.KST.Comparison.standardSimplexIdentityElementIsInitial

#check @SerrePositivity.KST.Comparison.standardSimplexLocalCoefficientTrivialization
#print axioms SerrePositivity.KST.Comparison.standardSimplexLocalCoefficientTrivialization

#check @SerrePositivity.KST.Comparison.localCoefficientChainsIso
#print axioms SerrePositivity.KST.Comparison.localCoefficientChainsIso

#check @SerrePositivity.KST.Comparison.localCoefficientHomologyIso
#print axioms SerrePositivity.KST.Comparison.localCoefficientHomologyIso


-- LocalCoefficients.lean

#check @SerrePositivity.KST.Comparison.LocalCoefficientSystem
#print axioms SerrePositivity.KST.Comparison.LocalCoefficientSystem

#check @SerrePositivity.KST.Comparison.coefficientSimplicialFunctor
#print axioms SerrePositivity.KST.Comparison.coefficientSimplicialFunctor

#check @SerrePositivity.KST.Comparison.localCoefficientChains
#print axioms SerrePositivity.KST.Comparison.localCoefficientChains

#check @SerrePositivity.KST.Comparison.localCoefficientHomology
#print axioms SerrePositivity.KST.Comparison.localCoefficientHomology

#check @SerrePositivity.KST.Comparison.pullbackLocalCoefficients
#print axioms SerrePositivity.KST.Comparison.pullbackLocalCoefficients

#check @SerrePositivity.KST.Comparison.localCoefficientSimplicialMap
#print axioms SerrePositivity.KST.Comparison.localCoefficientSimplicialMap

#check @SerrePositivity.KST.Comparison.localCoefficientChainsMap
#print axioms SerrePositivity.KST.Comparison.localCoefficientChainsMap

#check @SerrePositivity.KST.Comparison.localCoefficientHomologyMap
#print axioms SerrePositivity.KST.Comparison.localCoefficientHomologyMap

#check @SerrePositivity.KST.Comparison.LocalHomologyIsomorphism
#print axioms SerrePositivity.KST.Comparison.LocalHomologyIsomorphism

#check @SerrePositivity.KST.Comparison.constantLocalCoefficients
#print axioms SerrePositivity.KST.Comparison.constantLocalCoefficients


-- LocalCoefficientsOver.lean

#check @SerrePositivity.KST.Comparison.overLocalCoefficientSourceIso
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientSourceIso

#check @SerrePositivity.KST.Comparison.coefficientWhiskerLeft_eqToHom
#print axioms SerrePositivity.KST.Comparison.coefficientWhiskerLeft_eqToHom

#check @SerrePositivity.KST.Comparison.overLocalCoefficientSourceIso_id
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientSourceIso_id

#check @SerrePositivity.KST.Comparison.overLocalCoefficientSourceIso_comp
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientSourceIso_comp

#check @SerrePositivity.KST.Comparison.overLocalCoefficientSimplicialMap
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientSimplicialMap

#check @SerrePositivity.KST.Comparison.overLocalCoefficientSimplicialMap_unit
#print axioms SerrePositivity.KST.Comparison.overLocalCoefficientSimplicialMap_unit


-- LocalizedCoproductMaps.lean

#check @SerrePositivity.KST.Comparison.coprodMap_left_localized_isIso
#print axioms SerrePositivity.KST.Comparison.coprodMap_left_localized_isIso

#check @SerrePositivity.KST.Comparison.coprodMap_right_localized_isIso
#print axioms SerrePositivity.KST.Comparison.coprodMap_right_localized_isIso

#check @SerrePositivity.KST.Comparison.coprodMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.coprodMap_localized_isIso


-- LocalizedHomotopyComparison.lean

#check @SerrePositivity.KST.Comparison.kanPiIsomorphism_of_localized_isIso
#print axioms SerrePositivity.KST.Comparison.kanPiIsomorphism_of_localized_isIso

#check @SerrePositivity.KST.Comparison.kanHomotopyEquivOfLocalizedIso
#print axioms SerrePositivity.KST.Comparison.kanHomotopyEquivOfLocalizedIso


-- LocalizedPushoutCube.lean

#check @SerrePositivity.KST.Comparison.pushoutMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.pushoutMap_localized_isIso


-- LoopFamily.lean

#check @SerrePositivity.KST.Comparison.const_basepoint
#print axioms SerrePositivity.KST.Comparison.const_basepoint

#check @SerrePositivity.KST.Comparison.parameterMappingPointed
#print axioms SerrePositivity.KST.Comparison.parameterMappingPointed

#check @SerrePositivity.KST.Comparison.loopFamily_boundary_map
#print axioms SerrePositivity.KST.Comparison.loopFamily_boundary_map

#check @SerrePositivity.KST.Comparison.loopFamily_boundary
#print axioms SerrePositivity.KST.Comparison.loopFamily_boundary

#check @SerrePositivity.KST.Comparison.loopFamilyCircle
#print axioms SerrePositivity.KST.Comparison.loopFamilyCircle

#check @SerrePositivity.KST.Comparison.parameterMappingTranspose
#print axioms SerrePositivity.KST.Comparison.parameterMappingTranspose

#check @SerrePositivity.KST.Comparison.parameterMappingTranspose_ι
#print axioms SerrePositivity.KST.Comparison.parameterMappingTranspose_ι

#check @SerrePositivity.KST.Comparison.loopFamilyMap
#print axioms SerrePositivity.KST.Comparison.loopFamilyMap

#check @SerrePositivity.KST.Comparison.loopFamilyMap_evaluation
#print axioms SerrePositivity.KST.Comparison.loopFamilyMap_evaluation


-- LoopPathPullback.lean

#check @SerrePositivity.KST.Comparison.loopPathFiberIso_hom_restriction
#print axioms SerrePositivity.KST.Comparison.loopPathFiberIso_hom_restriction

#check @SerrePositivity.KST.Comparison.loopPathRestriction_isPullback
#print axioms SerrePositivity.KST.Comparison.loopPathRestriction_isPullback


-- LoopPathRestriction.lean

#check @SerrePositivity.KST.Comparison.intervalCircleProjection
#print axioms SerrePositivity.KST.Comparison.intervalCircleProjection

#check @SerrePositivity.KST.Comparison.intervalCircleProjection_right
#print axioms SerrePositivity.KST.Comparison.intervalCircleProjection_right

#check @SerrePositivity.KST.Comparison.loopPathRestriction
#print axioms SerrePositivity.KST.Comparison.loopPathRestriction

#check @SerrePositivity.KST.Comparison.loopPathRestriction_ι
#print axioms SerrePositivity.KST.Comparison.loopPathRestriction_ι


-- MappingCylinder.lean

#check @SerrePositivity.KST.Comparison.mappingCylinder
#print axioms SerrePositivity.KST.Comparison.mappingCylinder

#check @SerrePositivity.KST.Comparison.mappingCylinderTop
#print axioms SerrePositivity.KST.Comparison.mappingCylinderTop

#check @SerrePositivity.KST.Comparison.mappingCylinderBase
#print axioms SerrePositivity.KST.Comparison.mappingCylinderBase

#check @SerrePositivity.KST.Comparison.mappingCylinderEndpoint
#print axioms SerrePositivity.KST.Comparison.mappingCylinderEndpoint

#check @SerrePositivity.KST.Comparison.mappingCylinderRetraction
#print axioms SerrePositivity.KST.Comparison.mappingCylinderRetraction

#check @SerrePositivity.KST.Comparison.mappingCylinderTop_retraction
#print axioms SerrePositivity.KST.Comparison.mappingCylinderTop_retraction

#check @SerrePositivity.KST.Comparison.mappingCylinderBase_retraction
#print axioms SerrePositivity.KST.Comparison.mappingCylinderBase_retraction

#check @SerrePositivity.KST.Comparison.mappingCylinderEndpoint_retraction
#print axioms SerrePositivity.KST.Comparison.mappingCylinderEndpoint_retraction

#check @SerrePositivity.KST.Comparison.mappingCylinderBase_anodyne
#print axioms SerrePositivity.KST.Comparison.mappingCylinderBase_anodyne

#check @SerrePositivity.KST.Comparison.mappingCylinderRetraction_localized_isIso
#print axioms SerrePositivity.KST.Comparison.mappingCylinderRetraction_localized_isIso


-- MappingCylinderDouble.lean

#check @SerrePositivity.KST.Comparison.mappingCylinderToDouble
#print axioms SerrePositivity.KST.Comparison.mappingCylinderToDouble

#check @SerrePositivity.KST.Comparison.mappingCylinderTop_toDouble
#print axioms SerrePositivity.KST.Comparison.mappingCylinderTop_toDouble

#check @SerrePositivity.KST.Comparison.mappingCylinderBase_toDouble
#print axioms SerrePositivity.KST.Comparison.mappingCylinderBase_toDouble

#check @SerrePositivity.KST.Comparison.mappingCylinderEndpoint_toDouble
#print axioms SerrePositivity.KST.Comparison.mappingCylinderEndpoint_toDouble

#check @SerrePositivity.KST.Comparison.mappingCylinderToDouble_isPushout
#print axioms SerrePositivity.KST.Comparison.mappingCylinderToDouble_isPushout


-- MatrixHomotopyProduct.lean

#check @SerrePositivity.KST.Comparison.matrixHomotopyEntryHom
#print axioms SerrePositivity.KST.Comparison.matrixHomotopyEntryHom

#check @SerrePositivity.KST.Comparison.matrixHomotopyEntryHom_bijective
#print axioms SerrePositivity.KST.Comparison.matrixHomotopyEntryHom_bijective

#check @SerrePositivity.KST.Comparison.matrixPositiveHomotopyMulEquiv
#print axioms SerrePositivity.KST.Comparison.matrixPositiveHomotopyMulEquiv


-- MatrixPointedSimplex.lean

#check @SerrePositivity.KST.Comparison.matrixMap_ext
#print axioms SerrePositivity.KST.Comparison.matrixMap_ext

#check @SerrePositivity.KST.Comparison.matrixMapOfEntries_entry
#print axioms SerrePositivity.KST.Comparison.matrixMapOfEntries_entry

#check @SerrePositivity.KST.Comparison.matrixPtSimplex
#print axioms SerrePositivity.KST.Comparison.matrixPtSimplex

#check @SerrePositivity.KST.Comparison.matrixPtSimplex_entry
#print axioms SerrePositivity.KST.Comparison.matrixPtSimplex_entry

#check @SerrePositivity.KST.Comparison.matrixRelStruct
#print axioms SerrePositivity.KST.Comparison.matrixRelStruct


-- MatrixSpace.lean

#check @SerrePositivity.KST.Comparison.matrixRingObject
#print axioms SerrePositivity.KST.Comparison.matrixRingObject

#check @SerrePositivity.KST.Comparison.matrixSpace
#print axioms SerrePositivity.KST.Comparison.matrixSpace

#check @SerrePositivity.KST.Comparison.matrixEntryMap
#print axioms SerrePositivity.KST.Comparison.matrixEntryMap

#check @SerrePositivity.KST.Comparison.matrixMapOfEntries
#print axioms SerrePositivity.KST.Comparison.matrixMapOfEntries

#check @SerrePositivity.KST.Comparison.matrixSpace_kanComplex
#print axioms SerrePositivity.KST.Comparison.matrixSpace_kanComplex


-- MatrixStabilization.lean

#check @SerrePositivity.KST.Comparison.matrixBlockUnit
#print axioms SerrePositivity.KST.Comparison.matrixBlockUnit

#check @SerrePositivity.KST.Comparison.matrixStabilization
#print axioms SerrePositivity.KST.Comparison.matrixStabilization

#check @SerrePositivity.KST.Comparison.matrixBlockUnit_map
#print axioms SerrePositivity.KST.Comparison.matrixBlockUnit_map

#check @SerrePositivity.KST.Comparison.matrixStabilization_map
#print axioms SerrePositivity.KST.Comparison.matrixStabilization_map


-- MatrixZeroStabilization.lean

#check @SerrePositivity.KST.Comparison.matrixZeroStabilization
#print axioms SerrePositivity.KST.Comparison.matrixZeroStabilization

#check @SerrePositivity.KST.Comparison.matrixZeroStabilization_map
#print axioms SerrePositivity.KST.Comparison.matrixZeroStabilization_map

#check @SerrePositivity.KST.Comparison.matrixStabilization_sub_one
#print axioms SerrePositivity.KST.Comparison.matrixStabilization_sub_one

#check @SerrePositivity.KST.Comparison.matrixZeroStabilizationMap
#print axioms SerrePositivity.KST.Comparison.matrixZeroStabilizationMap


-- MonoBasePullback.lean

#check @SerrePositivity.KST.Comparison.monoBasePullback_fst_snd
#print axioms SerrePositivity.KST.Comparison.monoBasePullback_fst_snd

#check @SerrePositivity.KST.Comparison.monoBasePullbackIso
#print axioms SerrePositivity.KST.Comparison.monoBasePullbackIso

#check @SerrePositivity.KST.Comparison.monoBasePullbackIso_inv_snd
#print axioms SerrePositivity.KST.Comparison.monoBasePullbackIso_inv_snd


-- MonoSpanGluing.lean

#check @SerrePositivity.KST.Comparison.spanCylinder_vertex_homotopyPullback_of_mono
#print axioms SerrePositivity.KST.Comparison.spanCylinder_vertex_homotopyPullback_of_mono


-- MonoidComponentMaps.lean

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.componentsMap
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.componentsMap

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.isGrouplike_of_components_surjective
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.isGrouplike_of_components_surjective

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.componentsMulEquiv
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.componentsMulEquiv


-- MonoidComponents.lean

#check @SerrePositivity.KST.Comparison.monoidSpace
#print axioms SerrePositivity.KST.Comparison.monoidSpace

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.edgeMul
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.edgeMul

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.componentsMul
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.componentsMul

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.componentsMonoid
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.componentsMonoid

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.IsGrouplike
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.IsGrouplike

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.componentsGroup
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.componentsGroup


-- MonoidComponentsAdjunction.lean

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.componentsExtend
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.componentsExtend

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.componentsExtend_desc
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.componentsExtend_desc

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.componentsDesc_extend
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.componentsDesc_extend

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.componentsHomEquiv
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.componentsHomEquiv

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.componentsConstAdjunction
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.componentsConstAdjunction

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.componentsFunctor_isLeftAdjoint
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.componentsFunctor_isLeftAdjoint


-- MonoidComponentsDescent.lean

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.constantMap_edge
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.constantMap_edge

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.componentsDesc
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.componentsDesc

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.simplexToComponents_zero
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.simplexToComponents_zero


-- MonoidComponentsFunctor.lean

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.componentsObject
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.componentsObject

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.componentsFunctor
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.componentsFunctor

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.vertexToComponents
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.vertexToComponents

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.simplexToComponents
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.simplexToComponents

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.simplexToComponents_natural
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.simplexToComponents_natural

#check @SerrePositivity.KST.Comparison.SimplicialMonoid.toComponents
#print axioms SerrePositivity.KST.Comparison.SimplicialMonoid.toComponents


-- MonoidPointedColimit.lean

#check @SerrePositivity.KST.Comparison.monoidSpaceFunctor
#print axioms SerrePositivity.KST.Comparison.monoidSpaceFunctor

#check @SerrePositivity.KST.Comparison.monoidSpaceFunctor_preservesSequentialColimits
#print axioms SerrePositivity.KST.Comparison.monoidSpaceFunctor_preservesSequentialColimits

#check @SerrePositivity.KST.Comparison.monoidPointedFunctor
#print axioms SerrePositivity.KST.Comparison.monoidPointedFunctor

#check @SerrePositivity.KST.Comparison.monoidPointed_kanComplex
#print axioms SerrePositivity.KST.Comparison.monoidPointed_kanComplex

#check @SerrePositivity.KST.Comparison.monoidPointed_basepoint
#print axioms SerrePositivity.KST.Comparison.monoidPointed_basepoint


-- MonoidTranslations.lean

#check @SerrePositivity.KST.Comparison.monoidMultiplication
#print axioms SerrePositivity.KST.Comparison.monoidMultiplication

#check @SerrePositivity.KST.Comparison.monoidLeftTranslation
#print axioms SerrePositivity.KST.Comparison.monoidLeftTranslation

#check @SerrePositivity.KST.Comparison.monoidLeftTranslation_one
#print axioms SerrePositivity.KST.Comparison.monoidLeftTranslation_one

#check @SerrePositivity.KST.Comparison.monoidLeftTranslation_comp
#print axioms SerrePositivity.KST.Comparison.monoidLeftTranslation_comp

#check @SerrePositivity.KST.Comparison.monoidLeftTranslationHomotopy
#print axioms SerrePositivity.KST.Comparison.monoidLeftTranslationHomotopy

#check @SerrePositivity.KST.Comparison.monoidTranslationClass
#print axioms SerrePositivity.KST.Comparison.monoidTranslationClass

#check @SerrePositivity.KST.Comparison.monoidLeftTranslation_map_eq
#print axioms SerrePositivity.KST.Comparison.monoidLeftTranslation_map_eq

#check @SerrePositivity.KST.Comparison.grouplikeTranslationIso
#print axioms SerrePositivity.KST.Comparison.grouplikeTranslationIso


-- MorphismPropertyColimits.lean

#check @SerrePositivity.KST.Comparison.morphismProperty_inverseImage_stableColimits
#print axioms SerrePositivity.KST.Comparison.morphismProperty_inverseImage_stableColimits


-- NerveChainsLastVertex.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.nerveChainsExUnit_lastVertex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.nerveChainsExUnit_lastVertex

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionNerveChains_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionNerveChains_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionNerveChains_lastVertex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionNerveChains_lastVertex


-- NerveLoopMultiplication.lean

#check @SerrePositivity.KST.Comparison.monoidNervePoint
#print axioms SerrePositivity.KST.Comparison.monoidNervePoint

#check @SerrePositivity.KST.Comparison.monoidNerveEdge_face
#print axioms SerrePositivity.KST.Comparison.monoidNerveEdge_face

#check @SerrePositivity.KST.Comparison.monoidNerveLoop
#print axioms SerrePositivity.KST.Comparison.monoidNerveLoop

#check @SerrePositivity.KST.Comparison.monoidNerveLoopMulStruct
#print axioms SerrePositivity.KST.Comparison.monoidNerveLoopMulStruct

#check @SerrePositivity.KST.Comparison.monoidNerveFundamentalClass
#print axioms SerrePositivity.KST.Comparison.monoidNerveFundamentalClass

#check @SerrePositivity.KST.Comparison.monoidNerveFundamentalClass_mul
#print axioms SerrePositivity.KST.Comparison.monoidNerveFundamentalClass_mul

#check @SerrePositivity.KST.Comparison.monoidNerveLoop_one
#print axioms SerrePositivity.KST.Comparison.monoidNerveLoop_one

#check @SerrePositivity.KST.Comparison.monoidNerveFundamentalClass_one
#print axioms SerrePositivity.KST.Comparison.monoidNerveFundamentalClass_one

#check @SerrePositivity.KST.Comparison.monoidNerveFundamentalOppositeHom
#print axioms SerrePositivity.KST.Comparison.monoidNerveFundamentalOppositeHom

#check @SerrePositivity.KST.Comparison.groupNerveFundamentalHom
#print axioms SerrePositivity.KST.Comparison.groupNerveFundamentalHom


-- NondegenerateCoefficientChains.lean

#check @SerrePositivity.KST.Comparison.nondegenerateCoefficientChainsIso
#print axioms SerrePositivity.KST.Comparison.nondegenerateCoefficientChainsIso

#check @SerrePositivity.KST.Comparison.nondegenerateCoefficientChainsIso_inv
#print axioms SerrePositivity.KST.Comparison.nondegenerateCoefficientChainsIso_inv

#check @SerrePositivity.KST.Comparison.nondegenerateCoefficientChainsIso_inv_naturality
#print axioms SerrePositivity.KST.Comparison.nondegenerateCoefficientChainsIso_inv_naturality

#check @SerrePositivity.KST.Comparison.constantLocalCoefficientNondegenerateIso
#print axioms SerrePositivity.KST.Comparison.constantLocalCoefficientNondegenerateIso


-- OrderNerveContraction.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveSubcomplex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveSubcomplex

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderIntervalMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderIntervalMap

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveHomotopyMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveHomotopyMap

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveHomotopyMap_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveHomotopyMap_zero

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveHomotopyMap_one
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveHomotopyMap_one

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveHomotopyMap_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveHomotopyMap_mem

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveSubcomplex_anodyne
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveSubcomplex_anodyne


-- OrderNerveSubcomplexIso.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderSubtypeInclusion
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderSubtypeInclusion

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveSubcomplexIso
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveSubcomplexIso

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveSubcomplexIso_inclusion
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderNerveSubcomplexIso_inclusion

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderSubtypeNerve_anodyne
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.orderSubtypeNerve_anodyne


-- OverFinitePresentable.lean

#check @SerrePositivity.KST.Comparison.over_isFinitelyPresentable_of_left
#print axioms SerrePositivity.KST.Comparison.over_isFinitelyPresentable_of_left


-- OverHornGenerators.lean

#check @SerrePositivity.KST.Comparison.overHornMap
#print axioms SerrePositivity.KST.Comparison.overHornMap

#check @SerrePositivity.KST.Comparison.overHornGenerators
#print axioms SerrePositivity.KST.Comparison.overHornGenerators

#check @SerrePositivity.KST.Comparison.overHornGenerators_rlp_iff
#print axioms SerrePositivity.KST.Comparison.overHornGenerators_rlp_iff

#check @SerrePositivity.KST.Comparison.overHornGenerators_llp_of_anodyne
#print axioms SerrePositivity.KST.Comparison.overHornGenerators_llp_of_anodyne

#check @SerrePositivity.KST.Comparison.overHornGenerators_cellPresentation
#print axioms SerrePositivity.KST.Comparison.overHornGenerators_cellPresentation


-- OverHornLifting.lean

#check @SerrePositivity.KST.Comparison.hornOverMap
#print axioms SerrePositivity.KST.Comparison.hornOverMap

#check @SerrePositivity.KST.Comparison.over_lifting_of_underlying
#print axioms SerrePositivity.KST.Comparison.over_lifting_of_underlying

#check @SerrePositivity.KST.Comparison.underlying_rlp_of_over_horns
#print axioms SerrePositivity.KST.Comparison.underlying_rlp_of_over_horns


-- PairContractionAnodyne.lean

#check @SerrePositivity.KST.Comparison.intervalEndpoint_zero_eq
#print axioms SerrePositivity.KST.Comparison.intervalEndpoint_zero_eq

#check @SerrePositivity.KST.Comparison.intervalEndpoint_one_eq
#print axioms SerrePositivity.KST.Comparison.intervalEndpoint_one_eq

#check @SerrePositivity.KST.Comparison.intervalEndpoint_naturality
#print axioms SerrePositivity.KST.Comparison.intervalEndpoint_naturality

#check @SerrePositivity.KST.Comparison.subcomplex_pairContraction_anodyne
#print axioms SerrePositivity.KST.Comparison.subcomplex_pairContraction_anodyne

#check @SerrePositivity.KST.Comparison.subcomplex_inclusion_anodyne
#print axioms SerrePositivity.KST.Comparison.subcomplex_inclusion_anodyne


-- PairHomotopyLifting.lean

#check @SerrePositivity.KST.Comparison.intervalEndpoint
#print axioms SerrePositivity.KST.Comparison.intervalEndpoint

#check @SerrePositivity.KST.Comparison.pointTensorIso_naturality
#print axioms SerrePositivity.KST.Comparison.pointTensorIso_naturality

#check @SerrePositivity.KST.Comparison.intervalEndpoint_anodyne
#print axioms SerrePositivity.KST.Comparison.intervalEndpoint_anodyne

#check @SerrePositivity.KST.Comparison.interval_lift
#print axioms SerrePositivity.KST.Comparison.interval_lift

#check @SerrePositivity.KST.Comparison.relative_interval_lift
#print axioms SerrePositivity.KST.Comparison.relative_interval_lift


-- ParametrizedTranslations.lean

#check @SerrePositivity.KST.Comparison.monoidActionFamily
#print axioms SerrePositivity.KST.Comparison.monoidActionFamily

#check @SerrePositivity.KST.Comparison.monoidActionFamily_naturality
#print axioms SerrePositivity.KST.Comparison.monoidActionFamily_naturality

#check @SerrePositivity.KST.Comparison.monoidActionFamily_const
#print axioms SerrePositivity.KST.Comparison.monoidActionFamily_const

#check @SerrePositivity.KST.Comparison.monoidActionHomotopyMap
#print axioms SerrePositivity.KST.Comparison.monoidActionHomotopyMap

#check @SerrePositivity.KST.Comparison.monoidActionFamilyHomotopy
#print axioms SerrePositivity.KST.Comparison.monoidActionFamilyHomotopy

#check @SerrePositivity.KST.Comparison.monoidActionFamily_const_localized_isIso
#print axioms SerrePositivity.KST.Comparison.monoidActionFamily_const_localized_isIso

#check @SerrePositivity.KST.Comparison.monoidActionFamily_simplex_localized_isIso
#print axioms SerrePositivity.KST.Comparison.monoidActionFamily_simplex_localized_isIso


-- PartialSectionAdjunct.lean

#check @SerrePositivity.KST.Comparison.partialSectionAdjunct
#print axioms SerrePositivity.KST.Comparison.partialSectionAdjunct

#check @SerrePositivity.KST.Comparison.partialSectionAdjunct_comp
#print axioms SerrePositivity.KST.Comparison.partialSectionAdjunct_comp

#check @SerrePositivity.KST.Comparison.partialSectionAdjunct_naturality
#print axioms SerrePositivity.KST.Comparison.partialSectionAdjunct_naturality

#check @SerrePositivity.KST.Comparison.partialSectionAdjunct_inclusion
#print axioms SerrePositivity.KST.Comparison.partialSectionAdjunct_inclusion

#check @SerrePositivity.KST.Comparison.partialSection_hom_ext
#print axioms SerrePositivity.KST.Comparison.partialSection_hom_ext


-- PartialSectionInclusion.lean

#check @SerrePositivity.KST.Comparison.partialSectionLiftMap
#print axioms SerrePositivity.KST.Comparison.partialSectionLiftMap

#check @SerrePositivity.KST.Comparison.partialSectionLiftMap_comp
#print axioms SerrePositivity.KST.Comparison.partialSectionLiftMap_comp

#check @SerrePositivity.KST.Comparison.partialSectionInclusionOver
#print axioms SerrePositivity.KST.Comparison.partialSectionInclusionOver

#check @SerrePositivity.KST.Comparison.partialSectionInclusion
#print axioms SerrePositivity.KST.Comparison.partialSectionInclusion

#check @SerrePositivity.KST.Comparison.partialSectionInclusion_base
#print axioms SerrePositivity.KST.Comparison.partialSectionInclusion_base

#check @SerrePositivity.KST.Comparison.partialSectionInclusionOver_fst
#print axioms SerrePositivity.KST.Comparison.partialSectionInclusionOver_fst


-- PartialSectionRestrictionLift.lean

#check @SerrePositivity.KST.Comparison.partialSectionRestrictionLift
#print axioms SerrePositivity.KST.Comparison.partialSectionRestrictionLift

#check @SerrePositivity.KST.Comparison.partialSectionRestrictionLift_comp
#print axioms SerrePositivity.KST.Comparison.partialSectionRestrictionLift_comp

#check @SerrePositivity.KST.Comparison.partialSectionRestrictionLiftOver
#print axioms SerrePositivity.KST.Comparison.partialSectionRestrictionLiftOver

#check @SerrePositivity.KST.Comparison.partialSectionRestrictionLiftOver_inclusion
#print axioms SerrePositivity.KST.Comparison.partialSectionRestrictionLiftOver_inclusion

#check @SerrePositivity.KST.Comparison.partialSectionRestrictionLift_inclusion
#print axioms SerrePositivity.KST.Comparison.partialSectionRestrictionLift_inclusion

#check @SerrePositivity.KST.Comparison.partialSectionRestrictionLift_unique
#print axioms SerrePositivity.KST.Comparison.partialSectionRestrictionLift_unique


-- PartialSections.lean

#check @SerrePositivity.KST.Comparison.partialSectionUnit
#print axioms SerrePositivity.KST.Comparison.partialSectionUnit

#check @SerrePositivity.KST.Comparison.partialSectionObject
#print axioms SerrePositivity.KST.Comparison.partialSectionObject

#check @SerrePositivity.KST.Comparison.partialSectionObject_allMono_rlp
#print axioms SerrePositivity.KST.Comparison.partialSectionObject_allMono_rlp


-- PiZeroRing.lean

#check @SerrePositivity.KST.Comparison.ringSpace
#print axioms SerrePositivity.KST.Comparison.ringSpace

#check @SerrePositivity.KST.Comparison.SimplicialRing.edgeAdd
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.edgeAdd

#check @SerrePositivity.KST.Comparison.SimplicialRing.edgeMul
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.edgeMul

#check @SerrePositivity.KST.Comparison.SimplicialRing.edgeNeg
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.edgeNeg

#check @SerrePositivity.KST.Comparison.SimplicialRing.edgeReverse
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.edgeReverse

#check @SerrePositivity.KST.Comparison.SimplicialRing.edgeConcat
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.edgeConcat

#check @SerrePositivity.KST.Comparison.SimplicialRing.nonempty_edge_of_mk_eq
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.nonempty_edge_of_mk_eq

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsAdd
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsAdd

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsMul
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsMul

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsAddInst
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsAddInst

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsMulInst
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsMulInst

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsZeroInst
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsZeroInst

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsOneInst
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsOneInst

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsNegInst
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsNegInst

#check @SerrePositivity.KST.Comparison.SimplicialRing.mk_add
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.mk_add

#check @SerrePositivity.KST.Comparison.SimplicialRing.mk_mul
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.mk_mul

#check @SerrePositivity.KST.Comparison.SimplicialRing.mk_neg
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.mk_neg

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsRing
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsRing

#check @SerrePositivity.KST.Comparison.SimplicialRing.toComponents
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.toComponents

#check @SerrePositivity.KST.Comparison.SimplicialRing.simplexToComponents
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.simplexToComponents

#check @SerrePositivity.KST.Comparison.SimplicialRing.simplexToComponents_natural
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.simplexToComponents_natural


-- PointedUnitEvaluation.lean

#check @SerrePositivity.KST.Comparison.pointedEvaluation_product
#print axioms SerrePositivity.KST.Comparison.pointedEvaluation_product

#check @SerrePositivity.KST.Comparison.pointedUnitIso_evaluation
#print axioms SerrePositivity.KST.Comparison.pointedUnitIso_evaluation


-- ProductHomotopyPullback.lean

#check @SerrePositivity.KST.Comparison.productPullbackSquare
#print axioms SerrePositivity.KST.Comparison.productPullbackSquare

#check @SerrePositivity.KST.Comparison.productProjection_rlp
#print axioms SerrePositivity.KST.Comparison.productProjection_rlp

#check @SerrePositivity.KST.Comparison.kanReplacement_kan
#print axioms SerrePositivity.KST.Comparison.kanReplacement_kan

#check @SerrePositivity.KST.Comparison.productPullback_isHomotopyPullback
#print axioms SerrePositivity.KST.Comparison.productPullback_isHomotopyPullback


-- RegularBar.lean

#check @SerrePositivity.KST.Comparison.RegularAction
#print axioms SerrePositivity.KST.Comparison.RegularAction

#check @SerrePositivity.KST.Comparison.regularActionCategory
#print axioms SerrePositivity.KST.Comparison.regularActionCategory

#check @SerrePositivity.KST.Comparison.regularActionProjection
#print axioms SerrePositivity.KST.Comparison.regularActionProjection

#check @SerrePositivity.KST.Comparison.regularActionMap
#print axioms SerrePositivity.KST.Comparison.regularActionMap

#check @SerrePositivity.KST.Comparison.regularActionContraction
#print axioms SerrePositivity.KST.Comparison.regularActionContraction

#check @SerrePositivity.KST.Comparison.regularActionNerveContraction
#print axioms SerrePositivity.KST.Comparison.regularActionNerveContraction

#check @SerrePositivity.KST.Comparison.regularActionFunctor
#print axioms SerrePositivity.KST.Comparison.regularActionFunctor

#check @SerrePositivity.KST.Comparison.bisimplicialRegularBar
#print axioms SerrePositivity.KST.Comparison.bisimplicialRegularBar

#check @SerrePositivity.KST.Comparison.regularBar
#print axioms SerrePositivity.KST.Comparison.regularBar

#check @SerrePositivity.KST.Comparison.RegularAction.mk
#print axioms SerrePositivity.KST.Comparison.RegularAction.mk

#check @SerrePositivity.KST.Comparison.RegularAction.val
#print axioms SerrePositivity.KST.Comparison.RegularAction.val


-- RegularBarContraction.lean

#check @SerrePositivity.KST.Comparison.regularAction_eqToHom_val
#print axioms SerrePositivity.KST.Comparison.regularAction_eqToHom_val

#check @SerrePositivity.KST.Comparison.regularAction_id_val
#print axioms SerrePositivity.KST.Comparison.regularAction_id_val

#check @SerrePositivity.KST.Comparison.regularAction_comp_val
#print axioms SerrePositivity.KST.Comparison.regularAction_comp_val

#check @SerrePositivity.KST.Comparison.regularActionInterval
#print axioms SerrePositivity.KST.Comparison.regularActionInterval

#check @SerrePositivity.KST.Comparison.regularActionInterval_map
#print axioms SerrePositivity.KST.Comparison.regularActionInterval_map

#check @SerrePositivity.KST.Comparison.regularBarContractionMap
#print axioms SerrePositivity.KST.Comparison.regularBarContractionMap

#check @SerrePositivity.KST.Comparison.regularBarBasepoint
#print axioms SerrePositivity.KST.Comparison.regularBarBasepoint

#check @SerrePositivity.KST.Comparison.regularBarContractionMap_one
#print axioms SerrePositivity.KST.Comparison.regularBarContractionMap_one

#check @SerrePositivity.KST.Comparison.regularBarContractionMap_zero
#print axioms SerrePositivity.KST.Comparison.regularBarContractionMap_zero

#check @SerrePositivity.KST.Comparison.regularBarContraction
#print axioms SerrePositivity.KST.Comparison.regularBarContraction


-- RegularBarFiber.lean

#check @SerrePositivity.KST.Comparison.regularBarStrictFiber
#print axioms SerrePositivity.KST.Comparison.regularBarStrictFiber

#check @SerrePositivity.KST.Comparison.regularBarFiberLift
#print axioms SerrePositivity.KST.Comparison.regularBarFiberLift

#check @SerrePositivity.KST.Comparison.regularBarStrictFiber_label
#print axioms SerrePositivity.KST.Comparison.regularBarStrictFiber_label

#check @SerrePositivity.KST.Comparison.regularBarStrictFiber_obj
#print axioms SerrePositivity.KST.Comparison.regularBarStrictFiber_obj

#check @SerrePositivity.KST.Comparison.regularBarFiberLift_bijective
#print axioms SerrePositivity.KST.Comparison.regularBarFiberLift_bijective

#check @SerrePositivity.KST.Comparison.regularBarFiberIso
#print axioms SerrePositivity.KST.Comparison.regularBarFiberIso

#check @SerrePositivity.KST.Comparison.regularBarFiber_isPullback
#print axioms SerrePositivity.KST.Comparison.regularBarFiber_isPullback


-- RegularBarHomotopyFiber.lean

#check @SerrePositivity.KST.Comparison.actionBarProjection_diagonal
#print axioms SerrePositivity.KST.Comparison.actionBarProjection_diagonal

#check @SerrePositivity.KST.Comparison.regularBarFiber_homotopyPullback
#print axioms SerrePositivity.KST.Comparison.regularBarFiber_homotopyPullback


-- RegularBarLoop.lean

#check @SerrePositivity.KST.Comparison.regularActionInterval_projection
#print axioms SerrePositivity.KST.Comparison.regularActionInterval_projection

#check @SerrePositivity.KST.Comparison.regularBarContraction_projection
#print axioms SerrePositivity.KST.Comparison.regularBarContraction_projection


-- RegularBarPathComparison.lean

#check @SerrePositivity.KST.Comparison.regularBarPathFamily
#print axioms SerrePositivity.KST.Comparison.regularBarPathFamily

#check @SerrePositivity.KST.Comparison.regularBarPathFamily_zero
#print axioms SerrePositivity.KST.Comparison.regularBarPathFamily_zero

#check @SerrePositivity.KST.Comparison.regularBarPathMap
#print axioms SerrePositivity.KST.Comparison.regularBarPathMap

#check @SerrePositivity.KST.Comparison.regularBarPathMap_endpoint
#print axioms SerrePositivity.KST.Comparison.regularBarPathMap_endpoint

#check @SerrePositivity.KST.Comparison.regularBar_terminal_localized_isIso
#print axioms SerrePositivity.KST.Comparison.regularBar_terminal_localized_isIso

#check @SerrePositivity.KST.Comparison.regularBarPathMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.regularBarPathMap_localized_isIso


-- RegularBarProjection.lean

#check @SerrePositivity.KST.Comparison.regularBarProjection
#print axioms SerrePositivity.KST.Comparison.regularBarProjection

#check @SerrePositivity.KST.Comparison.regularBarFiberMap
#print axioms SerrePositivity.KST.Comparison.regularBarFiberMap

#check @SerrePositivity.KST.Comparison.regularBarFiberMap_projection
#print axioms SerrePositivity.KST.Comparison.regularBarFiberMap_projection


-- RelativeLocalCoefficients.lean

#check @SerrePositivity.KST.Comparison.relativeOverLocalCoefficientChains
#print axioms SerrePositivity.KST.Comparison.relativeOverLocalCoefficientChains

#check @SerrePositivity.KST.Comparison.relativeOverLocalCoefficientChainsFunctor
#print axioms SerrePositivity.KST.Comparison.relativeOverLocalCoefficientChainsFunctor

#check @SerrePositivity.KST.Comparison.relativeOverLocalCoefficientHomology
#print axioms SerrePositivity.KST.Comparison.relativeOverLocalCoefficientHomology

#check @SerrePositivity.KST.Comparison.relativeOverLocalCoefficientSequence
#print axioms SerrePositivity.KST.Comparison.relativeOverLocalCoefficientSequence

#check @SerrePositivity.KST.Comparison.relativeOverLocalCoefficientSequence_shortExact
#print axioms SerrePositivity.KST.Comparison.relativeOverLocalCoefficientSequence_shortExact

#check @SerrePositivity.KST.Comparison.relativeOverLocalCoefficientBoundary
#print axioms SerrePositivity.KST.Comparison.relativeOverLocalCoefficientBoundary

#check @SerrePositivity.KST.Comparison.relativeOverLocalCoefficient_exact_at_target
#print axioms SerrePositivity.KST.Comparison.relativeOverLocalCoefficient_exact_at_target

#check @SerrePositivity.KST.Comparison.relativeOverLocalCoefficient_boundary_comp
#print axioms SerrePositivity.KST.Comparison.relativeOverLocalCoefficient_boundary_comp

#check @SerrePositivity.KST.Comparison.relativeOverLocalCoefficient_exact_at_source
#print axioms SerrePositivity.KST.Comparison.relativeOverLocalCoefficient_exact_at_source

#check @SerrePositivity.KST.Comparison.relativeOverLocalCoefficient_comp_boundary
#print axioms SerrePositivity.KST.Comparison.relativeOverLocalCoefficient_comp_boundary

#check @SerrePositivity.KST.Comparison.relativeOverLocalCoefficient_exact_at_relative
#print axioms SerrePositivity.KST.Comparison.relativeOverLocalCoefficient_exact_at_relative

#check @SerrePositivity.KST.Comparison.overLocalHomologyEquivalence_iff_relative_acyclic
#print axioms SerrePositivity.KST.Comparison.overLocalHomologyEquivalence_iff_relative_acyclic

#check @SerrePositivity.KST.Comparison.relativeOverLocalCoefficientPushoutIso
#print axioms SerrePositivity.KST.Comparison.relativeOverLocalCoefficientPushoutIso


-- ReplacementComparison.lean

#check @SerrePositivity.KST.Comparison.pullbackMapBase
#print axioms SerrePositivity.KST.Comparison.pullbackMapBase

#check @SerrePositivity.KST.Comparison.pullbackMapBase_fst
#print axioms SerrePositivity.KST.Comparison.pullbackMapBase_fst

#check @SerrePositivity.KST.Comparison.pullbackMapBase_snd
#print axioms SerrePositivity.KST.Comparison.pullbackMapBase_snd

#check @SerrePositivity.KST.Comparison.pullbackMapBase_comp
#print axioms SerrePositivity.KST.Comparison.pullbackMapBase_comp

#check @SerrePositivity.KST.Comparison.replacementComparison_pullback_isIso
#print axioms SerrePositivity.KST.Comparison.replacementComparison_pullback_isIso


-- RingBasepointTranslation.lean

#check @SerrePositivity.KST.Comparison.ringDegenerateVertex
#print axioms SerrePositivity.KST.Comparison.ringDegenerateVertex

#check @SerrePositivity.KST.Comparison.ringDegenerateVertex_natural
#print axioms SerrePositivity.KST.Comparison.ringDegenerateVertex_natural

#check @SerrePositivity.KST.Comparison.ringDegenerateVertex_zero
#print axioms SerrePositivity.KST.Comparison.ringDegenerateVertex_zero

#check @SerrePositivity.KST.Comparison.ringTranslationIso
#print axioms SerrePositivity.KST.Comparison.ringTranslationIso

#check @SerrePositivity.KST.Comparison.ringTranslationIso_basepoint
#print axioms SerrePositivity.KST.Comparison.ringTranslationIso_basepoint

#check @SerrePositivity.KST.Comparison.ringPositiveHomotopyBasepointEquiv
#print axioms SerrePositivity.KST.Comparison.ringPositiveHomotopyBasepointEquiv


-- RingHornCorrection.lean

#check @SerrePositivity.KST.Comparison.ringAddDegeneracy
#print axioms SerrePositivity.KST.Comparison.ringAddDegeneracy

#check @SerrePositivity.KST.Comparison.ringAddDegeneracy_face_self
#print axioms SerrePositivity.KST.Comparison.ringAddDegeneracy_face_self

#check @SerrePositivity.KST.Comparison.ringAddDegeneracy_face_succ
#print axioms SerrePositivity.KST.Comparison.ringAddDegeneracy_face_succ

#check @SerrePositivity.KST.Comparison.ringAddDegeneracy_preserves_low
#print axioms SerrePositivity.KST.Comparison.ringAddDegeneracy_preserves_low

#check @SerrePositivity.KST.Comparison.ringAddDegeneracy_preserves_high
#print axioms SerrePositivity.KST.Comparison.ringAddDegeneracy_preserves_high

#check @SerrePositivity.KST.Comparison.ringAddDegeneracy_correct_lower
#print axioms SerrePositivity.KST.Comparison.ringAddDegeneracy_correct_lower

#check @SerrePositivity.KST.Comparison.ringAddDegeneracy_correct_upper
#print axioms SerrePositivity.KST.Comparison.ringAddDegeneracy_correct_upper


-- RingHornFaces.lean

#check @SerrePositivity.KST.Comparison.RingHornFaces
#print axioms SerrePositivity.KST.Comparison.RingHornFaces

#check @SerrePositivity.KST.Comparison.RingHornFaces.ofCompatible
#print axioms SerrePositivity.KST.Comparison.RingHornFaces.ofCompatible

#check @SerrePositivity.KST.Comparison.RingHornFaces.error_face_low
#print axioms SerrePositivity.KST.Comparison.RingHornFaces.error_face_low

#check @SerrePositivity.KST.Comparison.RingHornFaces.error_face_high
#print axioms SerrePositivity.KST.Comparison.RingHornFaces.error_face_high


-- RingHornLower.lean

#check @SerrePositivity.KST.Comparison.RingHornFaces.correct_lower_step
#print axioms SerrePositivity.KST.Comparison.RingHornFaces.correct_lower_step

#check @SerrePositivity.KST.Comparison.RingHornFaces.exists_lower_prefix
#print axioms SerrePositivity.KST.Comparison.RingHornFaces.exists_lower_prefix


-- RingHornUpper.lean

#check @SerrePositivity.KST.Comparison.RingHornFaces.correct_upper_step
#print axioms SerrePositivity.KST.Comparison.RingHornFaces.correct_upper_step

#check @SerrePositivity.KST.Comparison.RingHornFaces.exists_filler
#print axioms SerrePositivity.KST.Comparison.RingHornFaces.exists_filler


-- SegalRealizationComparison.lean

#check @SerrePositivity.KST.Comparison.segalRealization_homotopyPullback
#print axioms SerrePositivity.KST.Comparison.segalRealization_homotopyPullback


-- SequenceHomotopyPullbacks.lean

#check @SerrePositivity.KST.Comparison.diagramArrow_id_homotopyPullback
#print axioms SerrePositivity.KST.Comparison.diagramArrow_id_homotopyPullback

#check @SerrePositivity.KST.Comparison.sequenceArrow_homotopyPullback_of_successors
#print axioms SerrePositivity.KST.Comparison.sequenceArrow_homotopyPullback_of_successors


-- SequentialFiberComparison.lean

#check @SerrePositivity.KST.Comparison.sequentialFiberComparison
#print axioms SerrePositivity.KST.Comparison.sequentialFiberComparison

#check @SerrePositivity.KST.Comparison.sequentialFiberComparison_app_localized_isIso
#print axioms SerrePositivity.KST.Comparison.sequentialFiberComparison_app_localized_isIso


-- SequentialHomotopyPullback.lean

#check @SerrePositivity.KST.Comparison.sequential_homotopyPullback
#print axioms SerrePositivity.KST.Comparison.sequential_homotopyPullback


-- SequentialKanColimit.lean

#check @SerrePositivity.KST.Comparison.sequentialColim_rlp
#print axioms SerrePositivity.KST.Comparison.sequentialColim_rlp

#check @SerrePositivity.KST.Comparison.sequentialColim_preservesPullbacks
#print axioms SerrePositivity.KST.Comparison.sequentialColim_preservesPullbacks


-- SimplexComponents.lean

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexVertex
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexVertex

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexVertex_class_eq
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexVertex_class_eq

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_map
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_map

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_zero
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass_zero


-- SimplexConeVertex.lean

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero_zero
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero_zero

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero_succ
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero_succ

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero_comp
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero_comp

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero_δ_zero
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero_δ_zero


-- SimplexContraction.lean

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContractionAt
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContractionAt

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContractionMap
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContractionMap

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContraction
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContraction

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexMapContraction
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexMapContraction


-- SimplexFaceRetraction.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.simplexFaceRetraction
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.simplexFaceRetraction

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.simplexFaceRetraction_section
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.simplexFaceRetraction_section

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.simplexFaceRetraction_recover
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.simplexFaceRetraction_recover

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.simplexFaceRetraction_chain
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.simplexFaceRetraction_chain


-- SimplexImageMono.lean

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_comp_mono
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_comp_mono

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_comp_mono_ι
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_comp_mono_ι

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexFactorThruImage_comp_mono
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexFactorThruImage_comp_mono

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_of_epi
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_of_epi

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_ι_of_epi
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_ι_of_epi

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexFactorThruImage_of_epi
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexFactorThruImage_of_epi


-- SimplexPrepend.lean

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_zero
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_zero

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_succ
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_succ

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_comp
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_comp

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_id
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_id

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_epi
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_epi

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_mono
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_mono


-- SimplexPrependRelations.lean

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_δ_zero
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_δ_zero

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_δ
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_δ

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_σ
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_σ


-- SimplicialCoproductMono.lean

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialMonoCoprod
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialMonoCoprod


-- SimplicialMonoidInternal.lean

#check @SerrePositivity.KST.Comparison.simplicialMonoidToInternal
#print axioms SerrePositivity.KST.Comparison.simplicialMonoidToInternal

#check @SerrePositivity.KST.Comparison.internalMonoidToSimplicial
#print axioms SerrePositivity.KST.Comparison.internalMonoidToSimplicial

#check @SerrePositivity.KST.Comparison.simplicialMonoidToInternal_space
#print axioms SerrePositivity.KST.Comparison.simplicialMonoidToInternal_space

#check @SerrePositivity.KST.Comparison.internalMonoidToSimplicial_space
#print axioms SerrePositivity.KST.Comparison.internalMonoidToSimplicial_space


-- SimplicialRingKan.lean

#check @SerrePositivity.KST.Comparison.ringSpace_kanComplex
#print axioms SerrePositivity.KST.Comparison.ringSpace_kanComplex


-- SimplicialSum.lean

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumDesc
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumDesc

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_desc
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_desc

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum_hom_ext
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum_hom_ext

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumIsCoproduct
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumIsCoproduct

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_map
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_map


-- SimplicialSumEquivalences.lean

#check @SerrePositivity.KST.Comparison.simplicialSumMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.simplicialSumMap_localized_isIso


-- SimplicialSumFibrations.lean

#check @SerrePositivity.KST.Comparison.simplicialSumMap_rlp
#print axioms SerrePositivity.KST.Comparison.simplicialSumMap_rlp


-- SimplicialSumHomotopyPullbacks.lean

#check @SerrePositivity.KST.Comparison.simplicialSumReindex_homotopyPullback_of_fibrations
#print axioms SerrePositivity.KST.Comparison.simplicialSumReindex_homotopyPullback_of_fibrations


-- SimplicialSumPullbacks.lean

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_reindex
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_reindex

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex_commSq
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex_commSq

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex_isPullback
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex_isPullback

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_isPullback
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_isPullback


-- SliceAdjunction.lean

#check @SerrePositivity.KST.Comparison.simplicialSliceClosed
#print axioms SerrePositivity.KST.Comparison.simplicialSliceClosed

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_isLeftAdjoint
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_isLeftAdjoint

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_map_fst
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_map_fst

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_map_snd
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_map_snd

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_map_isPullback
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_map_isPullback


-- SliceFiberPushouts.lean

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_preservesColimits
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_preservesColimits

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_isPushout
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_isPushout

#check @SerrePositivity.KST.Comparison.sliceFiberPushoutIso
#print axioms SerrePositivity.KST.Comparison.sliceFiberPushoutIso


-- SliceRightAdjointTrivialFibrations.lean

#check @SerrePositivity.KST.Comparison.underlying_rlp_of_over_monos
#print axioms SerrePositivity.KST.Comparison.underlying_rlp_of_over_monos

#check @SerrePositivity.KST.Comparison.sliceFiberRightAdjoint_allMono_rlp
#print axioms SerrePositivity.KST.Comparison.sliceFiberRightAdjoint_allMono_rlp


-- SpanCylinderColimit.lean

#check @SerrePositivity.KST.Comparison.spanCylinderToColimit
#print axioms SerrePositivity.KST.Comparison.spanCylinderToColimit

#check @SerrePositivity.KST.Comparison.spanCylinderLeft_toColimit
#print axioms SerrePositivity.KST.Comparison.spanCylinderLeft_toColimit

#check @SerrePositivity.KST.Comparison.spanCylinderRight_toColimit
#print axioms SerrePositivity.KST.Comparison.spanCylinderRight_toColimit

#check @SerrePositivity.KST.Comparison.spanCylinder_middle_toColimit
#print axioms SerrePositivity.KST.Comparison.spanCylinder_middle_toColimit

#check @SerrePositivity.KST.Comparison.spanCylinderVertex_toColimit
#print axioms SerrePositivity.KST.Comparison.spanCylinderVertex_toColimit

#check @SerrePositivity.KST.Comparison.spanCylinderToColimit_localized_isIso
#print axioms SerrePositivity.KST.Comparison.spanCylinderToColimit_localized_isIso


-- SpanCylinderColimitNaturality.lean

#check @SerrePositivity.KST.Comparison.spanCylinderToColimit_naturality
#print axioms SerrePositivity.KST.Comparison.spanCylinderToColimit_naturality

#check @SerrePositivity.KST.Comparison.spanColimit_map_localized_isIso
#print axioms SerrePositivity.KST.Comparison.spanColimit_map_localized_isIso


-- SpanCylinderFunctor.lean

#check @SerrePositivity.KST.Comparison.spanCylinderFunctor
#print axioms SerrePositivity.KST.Comparison.spanCylinderFunctor

#check @SerrePositivity.KST.Comparison.spanCylinderLeft
#print axioms SerrePositivity.KST.Comparison.spanCylinderLeft

#check @SerrePositivity.KST.Comparison.spanCylinderRight
#print axioms SerrePositivity.KST.Comparison.spanCylinderRight

#check @SerrePositivity.KST.Comparison.spanCylinderCenter
#print axioms SerrePositivity.KST.Comparison.spanCylinderCenter

#check @SerrePositivity.KST.Comparison.spanCylinderVertex
#print axioms SerrePositivity.KST.Comparison.spanCylinderVertex

#check @SerrePositivity.KST.Comparison.spanCylinderFunctor_map_localized_isIso
#print axioms SerrePositivity.KST.Comparison.spanCylinderFunctor_map_localized_isIso


-- SpanCylinderInvariance.lean

#check @SerrePositivity.KST.Comparison.naturalitySquare_map_iff
#print axioms SerrePositivity.KST.Comparison.naturalitySquare_map_iff

#check @SerrePositivity.KST.Comparison.spanCylinder_vertexSquare_map_iff
#print axioms SerrePositivity.KST.Comparison.spanCylinder_vertexSquare_map_iff


-- SpanGluing.lean

#check @SerrePositivity.KST.Comparison.spanCylinder_vertex_homotopyPullback_of_fibrations
#print axioms SerrePositivity.KST.Comparison.spanCylinder_vertex_homotopyPullback_of_fibrations

#check @SerrePositivity.KST.Comparison.spanCylinder_vertex_homotopyPullback
#print axioms SerrePositivity.KST.Comparison.spanCylinder_vertex_homotopyPullback


-- SpanMonoBase.lean

#check @SerrePositivity.KST.Comparison.spanMonoBase
#print axioms SerrePositivity.KST.Comparison.spanMonoBase

#check @SerrePositivity.KST.Comparison.spanMonoBaseProjection
#print axioms SerrePositivity.KST.Comparison.spanMonoBaseProjection

#check @SerrePositivity.KST.Comparison.spanMonoBase_fst_mono
#print axioms SerrePositivity.KST.Comparison.spanMonoBase_fst_mono

#check @SerrePositivity.KST.Comparison.spanMonoBase_snd_mono
#print axioms SerrePositivity.KST.Comparison.spanMonoBase_snd_mono

#check @SerrePositivity.KST.Comparison.spanMonoBase_zero_kanComplex
#print axioms SerrePositivity.KST.Comparison.spanMonoBase_zero_kanComplex

#check @SerrePositivity.KST.Comparison.spanMonoBaseProjection_localized_isIso
#print axioms SerrePositivity.KST.Comparison.spanMonoBaseProjection_localized_isIso


-- SpanPushoutGluing.lean

#check @SerrePositivity.KST.Comparison.spanPushout_vertex_homotopyPullback
#print axioms SerrePositivity.KST.Comparison.spanPushout_vertex_homotopyPullback


-- SpanStrictification.lean

#check @SerrePositivity.KST.Comparison.spanStrictification_of_mono
#print axioms SerrePositivity.KST.Comparison.spanStrictification_of_mono


-- StableGLComponents.lean

#check @SerrePositivity.KST.Comparison.hatGLInducedComponentsEquiv
#print axioms SerrePositivity.KST.Comparison.hatGLInducedComponentsEquiv

#check @SerrePositivity.KST.Comparison.generalLinearRankSequence
#print axioms SerrePositivity.KST.Comparison.generalLinearRankSequence

#check @SerrePositivity.KST.Comparison.stableGeneralLinear
#print axioms SerrePositivity.KST.Comparison.stableGeneralLinear

#check @SerrePositivity.KST.Comparison.hatGLInducedComponentsEquiv_stabilization
#print axioms SerrePositivity.KST.Comparison.hatGLInducedComponentsEquiv_stabilization

#check @SerrePositivity.KST.Comparison.hatGLRankComponentsIso
#print axioms SerrePositivity.KST.Comparison.hatGLRankComponentsIso

#check @SerrePositivity.KST.Comparison.stableHatGLComponentsIso
#print axioms SerrePositivity.KST.Comparison.stableHatGLComponentsIso


-- StableHatGL.lean

#check @SerrePositivity.KST.Comparison.hatGLRankSequence
#print axioms SerrePositivity.KST.Comparison.hatGLRankSequence

#check @SerrePositivity.KST.Comparison.stableHatGL
#print axioms SerrePositivity.KST.Comparison.stableHatGL

#check @SerrePositivity.KST.Comparison.stableHatGL_isGrouplike
#print axioms SerrePositivity.KST.Comparison.stableHatGL_isGrouplike

#check @SerrePositivity.KST.Comparison.stableHatGLGroupCompletionMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.stableHatGLGroupCompletionMap_localized_isIso


-- StableHatGLHigherComparison.lean

#check @SerrePositivity.KST.Comparison.monoidBarKanConnected
#print axioms SerrePositivity.KST.Comparison.monoidBarKanConnected

#check @SerrePositivity.KST.Comparison.stableHatGLCoefficientHomotopyIso
#print axioms SerrePositivity.KST.Comparison.stableHatGLCoefficientHomotopyIso

#check @SerrePositivity.KST.Comparison.stableHatGLCoefficientHomotopyMulEquiv
#print axioms SerrePositivity.KST.Comparison.stableHatGLCoefficientHomotopyMulEquiv

#check @SerrePositivity.KST.Comparison.lemma_2_13_pi_one
#print axioms SerrePositivity.KST.Comparison.lemma_2_13_pi_one

#check @SerrePositivity.KST.Comparison.lemma_2_13_higher
#print axioms SerrePositivity.KST.Comparison.lemma_2_13_higher


-- StableHatGLHomotopyColimit.lean

#check @SerrePositivity.KST.Comparison.liftedRankEquivalence
#print axioms SerrePositivity.KST.Comparison.liftedRankEquivalence

#check @SerrePositivity.KST.Comparison.liftedRank_isFiltered
#print axioms SerrePositivity.KST.Comparison.liftedRank_isFiltered

#check @SerrePositivity.KST.Comparison.stableHatGLLiftedPointedDiagram
#print axioms SerrePositivity.KST.Comparison.stableHatGLLiftedPointedDiagram

#check @SerrePositivity.KST.Comparison.stableHatGLLiftedPointedDiagram_kan
#print axioms SerrePositivity.KST.Comparison.stableHatGLLiftedPointedDiagram_kan

#check @SerrePositivity.KST.Comparison.stableHatGLLiftedPointedCocone
#print axioms SerrePositivity.KST.Comparison.stableHatGLLiftedPointedCocone

#check @SerrePositivity.KST.Comparison.stableHatGLLiftedPointedCocone_underlyingIsColimit
#print axioms SerrePositivity.KST.Comparison.stableHatGLLiftedPointedCocone_underlyingIsColimit

#check @SerrePositivity.KST.Comparison.stableHatGLLiftedPointedCocone_kan
#print axioms SerrePositivity.KST.Comparison.stableHatGLLiftedPointedCocone_kan

#check @SerrePositivity.KST.Comparison.stableHatGLHomotopyIsColimit
#print axioms SerrePositivity.KST.Comparison.stableHatGLHomotopyIsColimit


-- StableHatGLHomotopyGroupColimit.lean

#check @SerrePositivity.KST.Comparison.stableHatGLHomotopyGroupDiagram
#print axioms SerrePositivity.KST.Comparison.stableHatGLHomotopyGroupDiagram

#check @SerrePositivity.KST.Comparison.stableHatGLHomotopyGroupCocone
#print axioms SerrePositivity.KST.Comparison.stableHatGLHomotopyGroupCocone

#check @SerrePositivity.KST.Comparison.stableHatGLHomotopyGroupDiagram_hasColimit
#print axioms SerrePositivity.KST.Comparison.stableHatGLHomotopyGroupDiagram_hasColimit

#check @SerrePositivity.KST.Comparison.stableHatGLHomotopyGroupCocone_underlyingIsColimit
#print axioms SerrePositivity.KST.Comparison.stableHatGLHomotopyGroupCocone_underlyingIsColimit

#check @SerrePositivity.KST.Comparison.stableHatGLHomotopyGroupIsColimit
#print axioms SerrePositivity.KST.Comparison.stableHatGLHomotopyGroupIsColimit

#check @SerrePositivity.KST.Comparison.stableHatGLHomotopyGroupColimitIso
#print axioms SerrePositivity.KST.Comparison.stableHatGLHomotopyGroupColimitIso


-- StableHatGLKan.lean

#check @SerrePositivity.KST.Comparison.stableHatGLPointedCocone
#print axioms SerrePositivity.KST.Comparison.stableHatGLPointedCocone

#check @SerrePositivity.KST.Comparison.stableHatGLPointedCocone_underlyingIsColimit
#print axioms SerrePositivity.KST.Comparison.stableHatGLPointedCocone_underlyingIsColimit

#check @SerrePositivity.KST.Comparison.stableHatGL_kanComplex
#print axioms SerrePositivity.KST.Comparison.stableHatGL_kanComplex


-- StrictCylinderFibration.lean

#check @SerrePositivity.KST.Comparison.doubleMappingCylinderMap_rlp
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinderMap_rlp


-- StrictCylinderHomotopyPullbacks.lean

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_homotopyPullbacks_of_strict
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_homotopyPullbacks_of_strict


-- StrictCylinderPullbacks.lean

#check @SerrePositivity.KST.Comparison.doubleMappingCylinderMap_isPullback
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinderMap_isPullback

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_left_isPullback
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_left_isPullback

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_right_isPullback
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_right_isPullback

#check @SerrePositivity.KST.Comparison.cylinderZero_isPullback
#print axioms SerrePositivity.KST.Comparison.cylinderZero_isPullback

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_center_isPullback
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_center_isPullback


-- StrictPushoutCube.lean

#check @SerrePositivity.KST.Comparison.strictPushoutCube
#print axioms SerrePositivity.KST.Comparison.strictPushoutCube

#check @SerrePositivity.KST.Comparison.doubleMappingCylinderMap_strictCube
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinderMap_strictCube


-- SubcomplexContraction.lean

#check @SerrePositivity.KST.Comparison.localized_interval_endpoints
#print axioms SerrePositivity.KST.Comparison.localized_interval_endpoints

#check @SerrePositivity.KST.Comparison.subcomplex_inclusion_localized_isIso
#print axioms SerrePositivity.KST.Comparison.subcomplex_inclusion_localized_isIso


-- SubcomplexDistributive.lean

#check @SerrePositivity.KST.Comparison.subcomplexDistribLattice
#print axioms SerrePositivity.KST.Comparison.subcomplexDistribLattice


-- SubcomplexPreimageIso.lean

#check @SerrePositivity.KST.Comparison.subcomplexPreimageIsoOfLE
#print axioms SerrePositivity.KST.Comparison.subcomplexPreimageIsoOfLE

#check @SerrePositivity.KST.Comparison.subcomplexPreimageIsoOfLE_hom_ι
#print axioms SerrePositivity.KST.Comparison.subcomplexPreimageIsoOfLE_hom_ι


-- SubcomplexUnionCocone.lean

#check @SerrePositivity.KST.Comparison.subcomplexUnionSpan
#print axioms SerrePositivity.KST.Comparison.subcomplexUnionSpan

#check @SerrePositivity.KST.Comparison.subcomplexUnionCocone
#print axioms SerrePositivity.KST.Comparison.subcomplexUnionCocone

#check @SerrePositivity.KST.Comparison.subcomplexUnionCoconeIsColimit
#print axioms SerrePositivity.KST.Comparison.subcomplexUnionCoconeIsColimit

#check @SerrePositivity.KST.Comparison.tensorLeft_mono_of_mono
#print axioms SerrePositivity.KST.Comparison.tensorLeft_mono_of_mono

#check @SerrePositivity.KST.Comparison.tensorSubcomplexUnionCocone
#print axioms SerrePositivity.KST.Comparison.tensorSubcomplexUnionCocone

#check @SerrePositivity.KST.Comparison.tensorSubcomplexUnionCoconeIsColimit
#print axioms SerrePositivity.KST.Comparison.tensorSubcomplexUnionCoconeIsColimit


-- SubdivisionAdjunctionSimplex.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionHomEquiv_app_down
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionHomEquiv_app_down


-- SubdivisionAnodyne.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionHorn_anodyne
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionHorn_anodyne

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ex_map_rlp
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ex_map_rlp

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivision_map_anodyne
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivision_map_anodyne


-- SubdivisionCommonFace.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCommonFace
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCommonFace


-- SubdivisionCommutation.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_le_iff_of_ne
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_le_iff_of_ne

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_cut
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_cut

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_cut
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_cut

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_cut_lt
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_cut_lt

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_cut_lt
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_cut_lt


-- SubdivisionCut.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChain_le_initialSegment
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChain_le_initialSegment

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_maximum
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_maximum

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_comp
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_comp

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_idempotent
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_idempotent

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_last
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_last

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_zero

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt_comp
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt_comp

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt_idempotent
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt_idempotent

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt_last
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt_last

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt_zero
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt_zero

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt_lastVertex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt_lastVertex


-- SubdivisionDegeneracy.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace_image_not_mem
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace_image_not_mem

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_face

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_face


-- SubdivisionDoubleDegeneracy.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_double
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_double

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_double
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_double

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_double_cut
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_double_cut


-- SubdivisionFaceCut.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_map_absorb
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_map_absorb

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace_above
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace_above

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt_face_absorb
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt_face_absorb


-- SubdivisionFaceDegeneracy.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace_special
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace_special

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_face_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_face_right

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_face_right
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_face_right


-- SubdivisionFaceLifting.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.simplexHom_factor_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.simplexHom_factor_face

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionFace_app_injective
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionFace_app_injective

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionFace_avoids
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionFace_avoids

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionFace_lift
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionFace_lift


-- SubdivisionFrontCut.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace_front_above
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedFace_front_above

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt_front_face_absorb
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionCutAt_front_face_absorb


-- SubdivisionFrontDegeneracy.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_front
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_front

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_front
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_front


-- SubdivisionFrontFace.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainFrontImage
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainFrontImage

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainFrontImage_maximum
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainFrontImage_maximum

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainFrontImage_singleton_ge
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainFrontImage_singleton_ge

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainFrontImage_of_max_ge
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainFrontImage_of_max_ge

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainFrontImage_absorb
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainFrontImage_absorb

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_front_absorb
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_front_absorb


-- SubdivisionIntervals.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_initialSegment
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_initialSegment

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_singleton
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_singleton

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_succ
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_succ

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_surjective
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_surjective

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_initialSegment
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_initialSegment

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_singleton
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_singleton


-- SubdivisionLastVertex.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainMaximum
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainMaximum

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainMaximum_map
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainMaximum_map

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertexAt
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertexAt

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertex_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertex_naturality

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertex

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainInitialSegment
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainInitialSegment

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainMaximum_initialSegment
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainMaximum_initialSegment

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionVertexSectionAt
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionVertexSectionAt

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionVertexSectionAt_lastVertex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionVertexSectionAt_lastVertex

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertexAt_epi
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertexAt_epi


-- SubdivisionLastVertexMap.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertexMap
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertexMap


-- SubdivisionLastVertexSimplex.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertexMap_on_simplex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertexMap_on_simplex

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertexMap_stdSimplex
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionLastVertexMap_stdSimplex


-- SubdivisionMaximum.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_maximum
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_maximum

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_face_ge
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.liftedDegeneracy_face_ge


-- SubdivisionNerveChains.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.nerveSimplexOrderHom
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.nerveSimplexOrderHom

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainMap_comp
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainMap_comp

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.nerveChainsExUnit
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.nerveChainsExUnit

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionNerveChains
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionNerveChains

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.nerveChainsExUnit_naturality
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.nerveChainsExUnit_naturality


-- SubdivisionRearDegeneracy.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_rear
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_rear

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_rear
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.subdivisionDegeneracyAt_rear


-- SubdivisionSimplexCover.lean

#check @_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.subdivisionSimplexCover
#print axioms _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.subdivisionSimplexCover


-- SubdivisionUnions.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_mem_iff
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_mem_iff

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_preservesUnion
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainCut_preservesUnion

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_mem_iff
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_mem_iff

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_preservesUnion
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.finiteChainDegeneracy_preservesUnion


-- TelescopeFunctor.lean

#check @SerrePositivity.KST.Comparison.telescopeSpanFunctor
#print axioms SerrePositivity.KST.Comparison.telescopeSpanFunctor

#check @SerrePositivity.KST.Comparison.telescopeFunctor
#print axioms SerrePositivity.KST.Comparison.telescopeFunctor

#check @SerrePositivity.KST.Comparison.telescopeEvenStage
#print axioms SerrePositivity.KST.Comparison.telescopeEvenStage

#check @SerrePositivity.KST.Comparison.telescopeOddStage
#print axioms SerrePositivity.KST.Comparison.telescopeOddStage

#check @SerrePositivity.KST.Comparison.telescopeFunctor_map_localized_isIso
#print axioms SerrePositivity.KST.Comparison.telescopeFunctor_map_localized_isIso


-- TelescopeGluing.lean

#check @SerrePositivity.KST.Comparison.telescopeSpan_homotopyPullbacks_of_fibrations
#print axioms SerrePositivity.KST.Comparison.telescopeSpan_homotopyPullbacks_of_fibrations

#check @SerrePositivity.KST.Comparison.telescopeStages_homotopyPullback_of_fibrations
#print axioms SerrePositivity.KST.Comparison.telescopeStages_homotopyPullback_of_fibrations

#check @SerrePositivity.KST.Comparison.telescopeStages_homotopyPullback
#print axioms SerrePositivity.KST.Comparison.telescopeStages_homotopyPullback


-- TelescopeSpan.lean

#check @SerrePositivity.KST.Comparison.telescopeEdgeDegree
#print axioms SerrePositivity.KST.Comparison.telescopeEdgeDegree

#check @SerrePositivity.KST.Comparison.telescopeEvenIndex
#print axioms SerrePositivity.KST.Comparison.telescopeEvenIndex

#check @SerrePositivity.KST.Comparison.telescopeOddIndex
#print axioms SerrePositivity.KST.Comparison.telescopeOddIndex

#check @SerrePositivity.KST.Comparison.telescopeEdgeDegree_le_even
#print axioms SerrePositivity.KST.Comparison.telescopeEdgeDegree_le_even

#check @SerrePositivity.KST.Comparison.telescopeEdgeDegree_le_odd
#print axioms SerrePositivity.KST.Comparison.telescopeEdgeDegree_le_odd

#check @SerrePositivity.KST.Comparison.telescopeSpan
#print axioms SerrePositivity.KST.Comparison.telescopeSpan

#check @SerrePositivity.KST.Comparison.telescopeSpanMap
#print axioms SerrePositivity.KST.Comparison.telescopeSpanMap


-- TensorBoundaryGluing.lean

#check @SerrePositivity.KST.Comparison.tensorBoundary_homotopyPullback_of_faces
#print axioms SerrePositivity.KST.Comparison.tensorBoundary_homotopyPullback_of_faces


-- TensorHomotopyPullbacks.lean

#check @SerrePositivity.KST.Comparison.tensorRight_isPullback
#print axioms SerrePositivity.KST.Comparison.tensorRight_isPullback

#check @SerrePositivity.KST.Comparison.isHomotopyPullback_tensorRight
#print axioms SerrePositivity.KST.Comparison.isHomotopyPullback_tensorRight


-- TensorRestriction.lean

#check @SerrePositivity.KST.Comparison.tensorRestrictionSquare
#print axioms SerrePositivity.KST.Comparison.tensorRestrictionSquare

#check @SerrePositivity.KST.Comparison.tensorRestriction_homotopyPullback_iff
#print axioms SerrePositivity.KST.Comparison.tensorRestriction_homotopyPullback_iff


-- TensorSubcomplexEmpty.lean

#check @SerrePositivity.KST.Comparison.tensorSubcomplex_homotopyPullback_bot
#print axioms SerrePositivity.KST.Comparison.tensorSubcomplex_homotopyPullback_bot


-- TensorSubcomplexFiniteCover.lean

#check @SerrePositivity.KST.Comparison.tensorSubcomplex_homotopyPullback_finset_sup
#print axioms SerrePositivity.KST.Comparison.tensorSubcomplex_homotopyPullback_finset_sup

#check @SerrePositivity.KST.Comparison.tensorSubcomplex_homotopyPullback_of_finset_cover
#print axioms SerrePositivity.KST.Comparison.tensorSubcomplex_homotopyPullback_of_finset_cover


-- TensorSubcomplexGluing.lean

#check @SerrePositivity.KST.Comparison.tensorSubcomplexSquare
#print axioms SerrePositivity.KST.Comparison.tensorSubcomplexSquare

#check @SerrePositivity.KST.Comparison.tensorSubcomplex_homotopyPullback_sup
#print axioms SerrePositivity.KST.Comparison.tensorSubcomplex_homotopyPullback_sup


-- TensorSubcomplexTop.lean

#check @SerrePositivity.KST.Comparison.tensorSubcomplex_homotopyPullback_top_iff
#print axioms SerrePositivity.KST.Comparison.tensorSubcomplex_homotopyPullback_top_iff


-- TranslationDescent.lean

#check @SerrePositivity.KST.Comparison.TranslationDescent.of_iso
#print axioms SerrePositivity.KST.Comparison.TranslationDescent.of_iso

#check @SerrePositivity.KST.Comparison.TranslationDescent.initial
#print axioms SerrePositivity.KST.Comparison.TranslationDescent.initial

#check @SerrePositivity.KST.Comparison.TranslationDescent.coproduct
#print axioms SerrePositivity.KST.Comparison.TranslationDescent.coproduct

#check @SerrePositivity.KST.Comparison.TranslationDescent.pushout
#print axioms SerrePositivity.KST.Comparison.TranslationDescent.pushout

#check @SerrePositivity.KST.Comparison.TranslationDescent.stage_isIso
#print axioms SerrePositivity.KST.Comparison.TranslationDescent.stage_isIso

#check @SerrePositivity.KST.Comparison.monoidActionFamily_localized_isIso
#print axioms SerrePositivity.KST.Comparison.monoidActionFamily_localized_isIso


-- TrivialFibrationExtension.lean

#check @SerrePositivity.KST.Comparison.partialSectionInclusion_isPullback
#print axioms SerrePositivity.KST.Comparison.partialSectionInclusion_isPullback

#check @SerrePositivity.KST.Comparison.partialSectionInclusion_mono
#print axioms SerrePositivity.KST.Comparison.partialSectionInclusion_mono

#check @SerrePositivity.KST.Comparison.trivialFibrationExtension
#print axioms SerrePositivity.KST.Comparison.trivialFibrationExtension


-- TwoCellCancellation.lean

#check @SerrePositivity.KST.Comparison.twoCellComplex_acyclic
#print axioms SerrePositivity.KST.Comparison.twoCellComplex_acyclic

#check @SerrePositivity.KST.Comparison.overLocalHomologyEquivalence_of_twoCellCancellation
#print axioms SerrePositivity.KST.Comparison.overLocalHomologyEquivalence_of_twoCellCancellation


-- UniqueFaceNondegenerate.lean

#check @SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.nonDegenerate_of_unique_face
#print axioms SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.nonDegenerate_of_unique_face
