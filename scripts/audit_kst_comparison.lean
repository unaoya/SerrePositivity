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


-- CartesianTensorSquare.lean

#check @SerrePositivity.KST.Comparison.cartesianTensorSquare_isPullback
#print axioms SerrePositivity.KST.Comparison.cartesianTensorSquare_isPullback


-- CommonTrivialRefinement.lean

#check @SerrePositivity.KST.Comparison.commonTrivialFibrationRefinement
#print axioms SerrePositivity.KST.Comparison.commonTrivialFibrationRefinement


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


-- CoproductPullbacks.lean

#check @SerrePositivity.KST.Comparison.coproductInclusions_isPullback
#print axioms SerrePositivity.KST.Comparison.coproductInclusions_isPullback

#check @SerrePositivity.KST.Comparison.binaryCoproductPullback
#print axioms SerrePositivity.KST.Comparison.binaryCoproductPullback

#check @SerrePositivity.KST.Comparison.coproductSquare_isPullback
#print axioms SerrePositivity.KST.Comparison.coproductSquare_isPullback


-- CutDegeneracy.lean

#check @SerrePositivity.KST.Comparison.finiteChainCutDegeneracy_singleton
#print axioms SerrePositivity.KST.Comparison.finiteChainCutDegeneracy_singleton

#check @SerrePositivity.KST.Comparison.liftedDegeneracy_le_castSucc_iff
#print axioms SerrePositivity.KST.Comparison.liftedDegeneracy_le_castSucc_iff

#check @SerrePositivity.KST.Comparison.liftedDegeneracy_le_succ_iff
#print axioms SerrePositivity.KST.Comparison.liftedDegeneracy_le_succ_iff


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

#check @SerrePositivity.KST.Comparison.liftedDegeneracy_val
#print axioms SerrePositivity.KST.Comparison.liftedDegeneracy_val

#check @SerrePositivity.KST.Comparison.liftedDegeneracy_next_fiber
#print axioms SerrePositivity.KST.Comparison.liftedDegeneracy_next_fiber

#check @SerrePositivity.KST.Comparison.liftedDegeneracy_self_fiber
#print axioms SerrePositivity.KST.Comparison.liftedDegeneracy_self_fiber

#check @SerrePositivity.KST.Comparison.liftedDegeneracy_castSucc
#print axioms SerrePositivity.KST.Comparison.liftedDegeneracy_castSucc


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

#check @SerrePositivity.KST.Comparison.cylinderEndpoints
#print axioms SerrePositivity.KST.Comparison.cylinderEndpoints

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_middle
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_middle

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_left
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_left

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_right
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_right

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_zero
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_zero

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_one
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_one


-- DoubleMappingCylinderEquivalence.lean

#check @SerrePositivity.KST.Comparison.cylinderEndpoints_naturality
#print axioms SerrePositivity.KST.Comparison.cylinderEndpoints_naturality

#check @SerrePositivity.KST.Comparison.doubleMappingCylinderMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinderMap_localized_isIso


-- DoubleMappingCylinderMap.lean

#check @SerrePositivity.KST.Comparison.doubleMappingCylinderMap
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinderMap

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_middle_map
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_middle_map

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_left_map
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_left_map

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_right_map
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_right_map

#check @SerrePositivity.KST.Comparison.doubleMappingCylinder_hom_ext
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinder_hom_ext

#check @SerrePositivity.KST.Comparison.doubleMappingCylinderMap_id
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinderMap_id

#check @SerrePositivity.KST.Comparison.doubleMappingCylinderMap_comp
#print axioms SerrePositivity.KST.Comparison.doubleMappingCylinderMap_comp


-- DoubleSubdivisionAdjunction.lean

#check @SerrePositivity.KST.Comparison.doubleSubdivisionHomEquiv
#print axioms SerrePositivity.KST.Comparison.doubleSubdivisionHomEquiv

#check @SerrePositivity.KST.Comparison.doubleSubdivisionHomEquiv_naturality_left
#print axioms SerrePositivity.KST.Comparison.doubleSubdivisionHomEquiv_naturality_left

#check @SerrePositivity.KST.Comparison.doubleSubdivisionHomEquiv_lastVertex
#print axioms SerrePositivity.KST.Comparison.doubleSubdivisionHomEquiv_lastVertex


-- DoubleSubdivisionHornBoundary.lean

#check @SerrePositivity.KST.Comparison.doubleSubdivisionHornMap_boundary
#print axioms SerrePositivity.KST.Comparison.doubleSubdivisionHornMap_boundary


-- DoubleSubdivisionHornMap.lean

#check @SerrePositivity.KST.Comparison.doubleSubdivisionHornMap
#print axioms SerrePositivity.KST.Comparison.doubleSubdivisionHornMap

#check @SerrePositivity.KST.Comparison.doubleSubdivisionHornMap_ι
#print axioms SerrePositivity.KST.Comparison.doubleSubdivisionHornMap_ι


-- ExComplexity.lean

#check @SerrePositivity.KST.Comparison.exComplexity
#print axioms SerrePositivity.KST.Comparison.exComplexity

#check @SerrePositivity.KST.Comparison.exComplexity_mono
#print axioms SerrePositivity.KST.Comparison.exComplexity_mono

#check @SerrePositivity.KST.Comparison.exComplexity_last
#print axioms SerrePositivity.KST.Comparison.exComplexity_last

#check @SerrePositivity.KST.Comparison.exComplexity_zero
#print axioms SerrePositivity.KST.Comparison.exComplexity_zero

#check @SerrePositivity.KST.Comparison.exComplexityLevel
#print axioms SerrePositivity.KST.Comparison.exComplexityLevel

#check @SerrePositivity.KST.Comparison.exComplexityLevel_mem
#print axioms SerrePositivity.KST.Comparison.exComplexityLevel_mem

#check @SerrePositivity.KST.Comparison.exComplexityLevel_le_iff
#print axioms SerrePositivity.KST.Comparison.exComplexityLevel_le_iff

#check @SerrePositivity.KST.Comparison.exComplexityLevel_zero_iff
#print axioms SerrePositivity.KST.Comparison.exComplexityLevel_zero_iff


-- ExDegeneracyExpansion.lean

#check @SerrePositivity.KST.Comparison.exComplexity_front_face
#print axioms SerrePositivity.KST.Comparison.exComplexity_front_face

#check @SerrePositivity.KST.Comparison.exExpansion_front_degeneracy
#print axioms SerrePositivity.KST.Comparison.exExpansion_front_degeneracy

#check @SerrePositivity.KST.Comparison.exExpansion_rear_degeneracy
#print axioms SerrePositivity.KST.Comparison.exExpansion_rear_degeneracy


-- ExDoubleHornFiller.lean

#check @SerrePositivity.KST.Comparison.exDoubleUniversalHornFiller
#print axioms SerrePositivity.KST.Comparison.exDoubleUniversalHornFiller

#check @SerrePositivity.KST.Comparison.exDoubleUniversalHornFiller_boundary
#print axioms SerrePositivity.KST.Comparison.exDoubleUniversalHornFiller_boundary

#check @SerrePositivity.KST.Comparison.exDoubleHornFiller
#print axioms SerrePositivity.KST.Comparison.exDoubleHornFiller

#check @SerrePositivity.KST.Comparison.exDoubleHornFiller_boundary
#print axioms SerrePositivity.KST.Comparison.exDoubleHornFiller_boundary


-- ExDoublePairing.lean

#check @SerrePositivity.KST.Comparison.exPairingStep_double
#print axioms SerrePositivity.KST.Comparison.exPairingStep_double

#check @SerrePositivity.KST.Comparison.exPairingStep_double_degenerate
#print axioms SerrePositivity.KST.Comparison.exPairingStep_double_degenerate

#check @SerrePositivity.KST.Comparison.exPairingStep_notMem_range_of_nonDegenerate
#print axioms SerrePositivity.KST.Comparison.exPairingStep_notMem_range_of_nonDegenerate


-- ExExpansionFaces.lean

#check @SerrePositivity.KST.Comparison.exExpansion_front_complexity
#print axioms SerrePositivity.KST.Comparison.exExpansion_front_complexity

#check @SerrePositivity.KST.Comparison.exExpansion_rear_face
#print axioms SerrePositivity.KST.Comparison.exExpansion_rear_face


-- ExExpansionSmallComplexity.lean

#check @SerrePositivity.KST.Comparison.exExpansion_eq_degeneracy_of_complexity_lt
#print axioms SerrePositivity.KST.Comparison.exExpansion_eq_degeneracy_of_complexity_lt

#check @SerrePositivity.KST.Comparison.exExpansion_degenerate_of_complexity_lt
#print axioms SerrePositivity.KST.Comparison.exExpansion_degenerate_of_complexity_lt


-- ExInfinity.lean

#check @SerrePositivity.KST.Comparison.exIterate
#print axioms SerrePositivity.KST.Comparison.exIterate

#check @SerrePositivity.KST.Comparison.exIterate_preservesFiniteLimits
#print axioms SerrePositivity.KST.Comparison.exIterate_preservesFiniteLimits

#check @SerrePositivity.KST.Comparison.exSequence
#print axioms SerrePositivity.KST.Comparison.exSequence

#check @SerrePositivity.KST.Comparison.exSequence_flip_preservesFiniteLimits
#print axioms SerrePositivity.KST.Comparison.exSequence_flip_preservesFiniteLimits

#check @SerrePositivity.KST.Comparison.exInfinity
#print axioms SerrePositivity.KST.Comparison.exInfinity

#check @SerrePositivity.KST.Comparison.exInfinity_preservesFiniteLimits
#print axioms SerrePositivity.KST.Comparison.exInfinity_preservesFiniteLimits

#check @SerrePositivity.KST.Comparison.exInfinityStage
#print axioms SerrePositivity.KST.Comparison.exInfinityStage

#check @SerrePositivity.KST.Comparison.exInfinityUnit
#print axioms SerrePositivity.KST.Comparison.exInfinityUnit


-- ExInfinityAnodyne.lean

#check @SerrePositivity.KST.Comparison.exInfinityAnodyneSequence
#print axioms SerrePositivity.KST.Comparison.exInfinityAnodyneSequence

#check @SerrePositivity.KST.Comparison.exInfinityUnit_anodyne
#print axioms SerrePositivity.KST.Comparison.exInfinityUnit_anodyne


-- ExInfinityBar.lean

#check @SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_bar_localized_isIso
#print axioms SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_bar_localized_isIso


-- ExInfinityFibrations.lean

#check @SerrePositivity.KST.Comparison.exIterate_map_rlp
#print axioms SerrePositivity.KST.Comparison.exIterate_map_rlp

#check @SerrePositivity.KST.Comparison.exInfinity_map_rlp
#print axioms SerrePositivity.KST.Comparison.exInfinity_map_rlp


-- ExInfinityGrouplike.lean

#check @SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_componentsMulEquiv
#print axioms SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_componentsMulEquiv

#check @SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_isGrouplike
#print axioms SerrePositivity.KST.Comparison.exInfinitySimplicialMonoid_isGrouplike


-- ExInfinityHomotopyPullback.lean

#check @SerrePositivity.KST.Comparison.isHomotopyPullback_exInfinity_iff
#print axioms SerrePositivity.KST.Comparison.isHomotopyPullback_exInfinity_iff


-- ExInfinityKan.lean

#check @SerrePositivity.KST.Comparison.exInfinity_hornFilling
#print axioms SerrePositivity.KST.Comparison.exInfinity_hornFilling

#check @SerrePositivity.KST.Comparison.exInfinity_kanComplex
#print axioms SerrePositivity.KST.Comparison.exInfinity_kanComplex


-- ExInfinityLocalization.lean

#check @SerrePositivity.KST.Comparison.exInfinity_preservesMonomorphisms
#print axioms SerrePositivity.KST.Comparison.exInfinity_preservesMonomorphisms

#check @SerrePositivity.KST.Comparison.exInfinityUnit_localized_isIso
#print axioms SerrePositivity.KST.Comparison.exInfinityUnit_localized_isIso

#check @SerrePositivity.KST.Comparison.exInfinityLocalizedUnitIso
#print axioms SerrePositivity.KST.Comparison.exInfinityLocalizedUnitIso

#check @SerrePositivity.KST.Comparison.exInfinity_map_localized_isIso_iff
#print axioms SerrePositivity.KST.Comparison.exInfinity_map_localized_isIso_iff


-- ExInfinityMonoidal.lean

#check @SerrePositivity.KST.Comparison.exInfinity_monoidal
#print axioms SerrePositivity.KST.Comparison.exInfinity_monoidal

#check @SerrePositivity.KST.Comparison.exInfinityUnit_isMonoidal
#print axioms SerrePositivity.KST.Comparison.exInfinityUnit_isMonoidal

#check @SerrePositivity.KST.Comparison.exInfinityMonoidFunctor
#print axioms SerrePositivity.KST.Comparison.exInfinityMonoidFunctor

#check @SerrePositivity.KST.Comparison.exInfinityMonoidUnit
#print axioms SerrePositivity.KST.Comparison.exInfinityMonoidUnit

#check @SerrePositivity.KST.Comparison.exInfinityMonoid_kanComplex
#print axioms SerrePositivity.KST.Comparison.exInfinityMonoid_kanComplex

#check @SerrePositivity.KST.Comparison.exInfinityMonoidUnit_hom
#print axioms SerrePositivity.KST.Comparison.exInfinityMonoidUnit_hom

#check @SerrePositivity.KST.Comparison.exInfinityMonoidUnit_localized_isIso
#print axioms SerrePositivity.KST.Comparison.exInfinityMonoidUnit_localized_isIso


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

#check @SerrePositivity.KST.Comparison.exInfinity_finite_factorization
#print axioms SerrePositivity.KST.Comparison.exInfinity_finite_factorization

#check @SerrePositivity.KST.Comparison.exInfinityStage_succ
#print axioms SerrePositivity.KST.Comparison.exInfinityStage_succ


-- ExPairingBijection.lean

#check @SerrePositivity.KST.Comparison.exTypeOne
#print axioms SerrePositivity.KST.Comparison.exTypeOne

#check @SerrePositivity.KST.Comparison.exPairingStep_mem_typeOne
#print axioms SerrePositivity.KST.Comparison.exPairingStep_mem_typeOne

#check @SerrePositivity.KST.Comparison.exPairingStep_mem_typeTwo_of_typeOne
#print axioms SerrePositivity.KST.Comparison.exPairingStep_mem_typeTwo_of_typeOne

#check @SerrePositivity.KST.Comparison.exPairingEquiv
#print axioms SerrePositivity.KST.Comparison.exPairingEquiv

#check @SerrePositivity.KST.Comparison.exPairingEquiv_apply
#print axioms SerrePositivity.KST.Comparison.exPairingEquiv_apply


-- ExPairingCore.lean

#check @SerrePositivity.KST.Comparison.exPairingCore
#print axioms SerrePositivity.KST.Comparison.exPairingCore

#check @SerrePositivity.KST.Comparison.exPairingCore_isProper
#print axioms SerrePositivity.KST.Comparison.exPairingCore_isProper

#check @SerrePositivity.KST.Comparison.exPairing
#print axioms SerrePositivity.KST.Comparison.exPairing


-- ExPairingFaceRank.lean

#check @SerrePositivity.KST.Comparison.exExpansion_notMem_typeTwo
#print axioms SerrePositivity.KST.Comparison.exExpansion_notMem_typeTwo

#check @SerrePositivity.KST.Comparison.exPairingStep_face_rank_lt_succ
#print axioms SerrePositivity.KST.Comparison.exPairingStep_face_rank_lt_succ

#check @SerrePositivity.KST.Comparison.exPairingStep_face_rank_lt
#print axioms SerrePositivity.KST.Comparison.exPairingStep_face_rank_lt


-- ExPairingFaceUniqueness.lean

#check @SerrePositivity.KST.Comparison.exExpansion_front_ne_source
#print axioms SerrePositivity.KST.Comparison.exExpansion_front_ne_source

#check @SerrePositivity.KST.Comparison.exExpansion_rear_ne_source
#print axioms SerrePositivity.KST.Comparison.exExpansion_rear_ne_source

#check @SerrePositivity.KST.Comparison.exPairingStep_face_unique_succ
#print axioms SerrePositivity.KST.Comparison.exPairingStep_face_unique_succ


-- ExPairingNondegenerate.lean

#check @SerrePositivity.KST.Comparison.exExpansion_mem_degenerate
#print axioms SerrePositivity.KST.Comparison.exExpansion_mem_degenerate

#check @SerrePositivity.KST.Comparison.exPairingStep_mem_degenerate
#print axioms SerrePositivity.KST.Comparison.exPairingStep_mem_degenerate

#check @SerrePositivity.KST.Comparison.exPairingStep_nonDegenerate_source
#print axioms SerrePositivity.KST.Comparison.exPairingStep_nonDegenerate_source


-- ExPairingProperness.lean

#check @SerrePositivity.KST.Comparison.exPairingImage
#print axioms SerrePositivity.KST.Comparison.exPairingImage

#check @SerrePositivity.KST.Comparison.exTypeTwo
#print axioms SerrePositivity.KST.Comparison.exTypeTwo

#check @SerrePositivity.KST.Comparison.exPairingStep_face_unique
#print axioms SerrePositivity.KST.Comparison.exPairingStep_face_unique

#check @SerrePositivity.KST.Comparison.exPairingStep_nonDegenerate_target
#print axioms SerrePositivity.KST.Comparison.exPairingStep_nonDegenerate_target

#check @SerrePositivity.KST.Comparison.exPairingStep_isUniquelyCodimOneFace
#print axioms SerrePositivity.KST.Comparison.exPairingStep_isUniquelyCodimOneFace


-- ExPairingRegular.lean

#check @SerrePositivity.KST.Comparison.exPairingWeakRank
#print axioms SerrePositivity.KST.Comparison.exPairingWeakRank

#check @SerrePositivity.KST.Comparison.exPairingCore_isRegular
#print axioms SerrePositivity.KST.Comparison.exPairingCore_isRegular

#check @SerrePositivity.KST.Comparison.exPairing_isRegular
#print axioms SerrePositivity.KST.Comparison.exPairing_isRegular


-- ExPairingStep.lean

#check @SerrePositivity.KST.Comparison.exExpansion
#print axioms SerrePositivity.KST.Comparison.exExpansion

#check @SerrePositivity.KST.Comparison.exExpansion_face
#print axioms SerrePositivity.KST.Comparison.exExpansion_face

#check @SerrePositivity.KST.Comparison.exExpansion_complexity
#print axioms SerrePositivity.KST.Comparison.exExpansion_complexity

#check @SerrePositivity.KST.Comparison.exComplexity_face
#print axioms SerrePositivity.KST.Comparison.exComplexity_face

#check @SerrePositivity.KST.Comparison.exPairingStep
#print axioms SerrePositivity.KST.Comparison.exPairingStep

#check @SerrePositivity.KST.Comparison.exPairingStep_injective
#print axioms SerrePositivity.KST.Comparison.exPairingStep_injective

#check @SerrePositivity.KST.Comparison.exPairingStep_complexity_iff
#print axioms SerrePositivity.KST.Comparison.exPairingStep_complexity_iff

#check @SerrePositivity.KST.Comparison.exPairingStep_complexityLevel
#print axioms SerrePositivity.KST.Comparison.exPairingStep_complexityLevel

#check @SerrePositivity.KST.Comparison.exPairingStep_mem_image_iff
#print axioms SerrePositivity.KST.Comparison.exPairingStep_mem_image_iff


-- ExUnit.lean

#check @SerrePositivity.KST.Comparison.exUnitAt
#print axioms SerrePositivity.KST.Comparison.exUnitAt

#check @SerrePositivity.KST.Comparison.exUnitAt_naturality
#print axioms SerrePositivity.KST.Comparison.exUnitAt_naturality

#check @SerrePositivity.KST.Comparison.exUnit
#print axioms SerrePositivity.KST.Comparison.exUnit

#check @SerrePositivity.KST.Comparison.exUnitAt_mono
#print axioms SerrePositivity.KST.Comparison.exUnitAt_mono


-- ExUnitAnodyne.lean

#check @SerrePositivity.KST.Comparison.exUnitRange_anodyne
#print axioms SerrePositivity.KST.Comparison.exUnitRange_anodyne

#check @SerrePositivity.KST.Comparison.exUnitAt_anodyne
#print axioms SerrePositivity.KST.Comparison.exUnitAt_anodyne


-- FaceIntervals.lean

#check @SerrePositivity.KST.Comparison.liftedFace_injective
#print axioms SerrePositivity.KST.Comparison.liftedFace_injective

#check @SerrePositivity.KST.Comparison.liftedFace_of_below
#print axioms SerrePositivity.KST.Comparison.liftedFace_of_below

#check @SerrePositivity.KST.Comparison.liftedFace_initialSegment_of_below
#print axioms SerrePositivity.KST.Comparison.liftedFace_initialSegment_of_below


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

#check @SerrePositivity.KST.Comparison.finiteChain_exists_greatest
#print axioms SerrePositivity.KST.Comparison.finiteChain_exists_greatest

#check @SerrePositivity.KST.Comparison.finiteChainGreatest
#print axioms SerrePositivity.KST.Comparison.finiteChainGreatest

#check @SerrePositivity.KST.Comparison.finiteChainGreatest_mem
#print axioms SerrePositivity.KST.Comparison.finiteChainGreatest_mem

#check @SerrePositivity.KST.Comparison.le_finiteChainGreatest
#print axioms SerrePositivity.KST.Comparison.le_finiteChainGreatest

#check @SerrePositivity.KST.Comparison.finiteChainGreatest_map
#print axioms SerrePositivity.KST.Comparison.finiteChainGreatest_map

#check @SerrePositivity.KST.Comparison.finiteChainGreatest_eq_maximum
#print axioms SerrePositivity.KST.Comparison.finiteChainGreatest_eq_maximum


-- FiniteChainIntervals.lean

#check @SerrePositivity.KST.Comparison.finiteChainMaximum_singleton
#print axioms SerrePositivity.KST.Comparison.finiteChainMaximum_singleton

#check @SerrePositivity.KST.Comparison.finiteChainMap_singleton
#print axioms SerrePositivity.KST.Comparison.finiteChainMap_singleton

#check @SerrePositivity.KST.Comparison.finiteChainInitialSegment_le_iff
#print axioms SerrePositivity.KST.Comparison.finiteChainInitialSegment_le_iff

#check @SerrePositivity.KST.Comparison.finiteChainInitialSegment_map
#print axioms SerrePositivity.KST.Comparison.finiteChainInitialSegment_map


-- FiniteChainUnion.lean

#check @SerrePositivity.KST.Comparison.finiteChainOfFinset
#print axioms SerrePositivity.KST.Comparison.finiteChainOfFinset

#check @SerrePositivity.KST.Comparison.finiteChainSingleton
#print axioms SerrePositivity.KST.Comparison.finiteChainSingleton

#check @SerrePositivity.KST.Comparison.finiteChainUnion
#print axioms SerrePositivity.KST.Comparison.finiteChainUnion

#check @SerrePositivity.KST.Comparison.PreservesFiniteChainUnion
#print axioms SerrePositivity.KST.Comparison.PreservesFiniteChainUnion

#check @SerrePositivity.KST.Comparison.finiteChainUnion_ext
#print axioms SerrePositivity.KST.Comparison.finiteChainUnion_ext

#check @SerrePositivity.KST.Comparison.PreservesFiniteChainUnion.comp
#print axioms SerrePositivity.KST.Comparison.PreservesFiniteChainUnion.comp

#check @SerrePositivity.KST.Comparison.finiteChainMap_preservesUnion
#print axioms SerrePositivity.KST.Comparison.finiteChainMap_preservesUnion


-- FiniteOperationsFibrations.lean

#check @SerrePositivity.KST.Comparison.tensorRight_fst_isPullback
#print axioms SerrePositivity.KST.Comparison.tensorRight_fst_isPullback

#check @SerrePositivity.KST.Comparison.tensorRight_rlp
#print axioms SerrePositivity.KST.Comparison.tensorRight_rlp

#check @SerrePositivity.KST.Comparison.coproductMap_rlp
#print axioms SerrePositivity.KST.Comparison.coproductMap_rlp


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


-- GrouplikeGL.lean

#check @SerrePositivity.KST.Comparison.hatGL_isGrouplike
#print axioms SerrePositivity.KST.Comparison.hatGL_isGrouplike


-- GrouplikeTranslations.lean

#check @SerrePositivity.KST.Comparison.grouplikeTranslation_localized_isIso
#print axioms SerrePositivity.KST.Comparison.grouplikeTranslation_localized_isIso


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

#check @SerrePositivity.KST.Comparison.hornChainVertex_map_hornFaces
#print axioms SerrePositivity.KST.Comparison.hornChainVertex_map_hornFaces

#check @SerrePositivity.KST.Comparison.hornChainToHorn_boundary
#print axioms SerrePositivity.KST.Comparison.hornChainToHorn_boundary


-- HornChainMissingVertex.lean

#check @SerrePositivity.KST.Comparison.hornChainVertex_common_missing
#print axioms SerrePositivity.KST.Comparison.hornChainVertex_common_missing


-- HornChainNerve.lean

#check @SerrePositivity.KST.Comparison.hornChainToSimplex
#print axioms SerrePositivity.KST.Comparison.hornChainToSimplex

#check @SerrePositivity.KST.Comparison.hornChainToSimplex_range_le
#print axioms SerrePositivity.KST.Comparison.hornChainToSimplex_range_le

#check @SerrePositivity.KST.Comparison.hornChainToHorn
#print axioms SerrePositivity.KST.Comparison.hornChainToHorn


-- HornChainVertices.lean

#check @SerrePositivity.KST.Comparison.HornFaceSet
#print axioms SerrePositivity.KST.Comparison.HornFaceSet

#check @SerrePositivity.KST.Comparison.hornFaceSet_of_le
#print axioms SerrePositivity.KST.Comparison.hornFaceSet_of_le

#check @SerrePositivity.KST.Comparison.hornFaceChoice
#print axioms SerrePositivity.KST.Comparison.hornFaceChoice

#check @SerrePositivity.KST.Comparison.hornChainVertex
#print axioms SerrePositivity.KST.Comparison.hornChainVertex

#check @SerrePositivity.KST.Comparison.hornChainVertex_exists_face
#print axioms SerrePositivity.KST.Comparison.hornChainVertex_exists_face

#check @SerrePositivity.KST.Comparison.hornChainVertex_of_all_faces
#print axioms SerrePositivity.KST.Comparison.hornChainVertex_of_all_faces


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

#check @SerrePositivity.KST.Comparison.hornFaceAddVertex
#print axioms SerrePositivity.KST.Comparison.hornFaceAddVertex

#check @SerrePositivity.KST.Comparison.hornFaceAddVertex_mem
#print axioms SerrePositivity.KST.Comparison.hornFaceAddVertex_mem

#check @SerrePositivity.KST.Comparison.hornFaceSingleton_mem
#print axioms SerrePositivity.KST.Comparison.hornFaceSingleton_mem

#check @SerrePositivity.KST.Comparison.hornFaceInclusion_anodyne
#print axioms SerrePositivity.KST.Comparison.hornFaceInclusion_anodyne


-- HornFaceNerveCover.lean

#check @SerrePositivity.KST.Comparison.hornFaceNerve_missingVertex
#print axioms SerrePositivity.KST.Comparison.hornFaceNerve_missingVertex

#check @SerrePositivity.KST.Comparison.hornFaceNerve_faceCover
#print axioms SerrePositivity.KST.Comparison.hornFaceNerve_faceCover


-- HornFacePoset.lean

#check @SerrePositivity.KST.Comparison.HornFacePoset
#print axioms SerrePositivity.KST.Comparison.HornFacePoset

#check @SerrePositivity.KST.Comparison.hornFacePoset_partialOrder
#print axioms SerrePositivity.KST.Comparison.hornFacePoset_partialOrder

#check @SerrePositivity.KST.Comparison.hornFaceInclusion
#print axioms SerrePositivity.KST.Comparison.hornFaceInclusion

#check @SerrePositivity.KST.Comparison.hornFacesToSimplex
#print axioms SerrePositivity.KST.Comparison.hornFacesToSimplex

#check @SerrePositivity.KST.Comparison.hornFacesToSimplex_range_le
#print axioms SerrePositivity.KST.Comparison.hornFacesToSimplex_range_le

#check @SerrePositivity.KST.Comparison.hornFacesLastVertex
#print axioms SerrePositivity.KST.Comparison.hornFacesLastVertex


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

#check @SerrePositivity.KST.Comparison.hornSimplexFaceFactorization
#print axioms SerrePositivity.KST.Comparison.hornSimplexFaceFactorization

#check @SerrePositivity.KST.Comparison.hornSubdivisionFaceCover
#print axioms SerrePositivity.KST.Comparison.hornSubdivisionFaceCover


-- HornSubdivisionComparison.lean

#check @SerrePositivity.KST.Comparison.hornSimplexOrderHom
#print axioms SerrePositivity.KST.Comparison.hornSimplexOrderHom

#check @SerrePositivity.KST.Comparison.hornSimplexOrderHom_map_mem
#print axioms SerrePositivity.KST.Comparison.hornSimplexOrderHom_map_mem

#check @SerrePositivity.KST.Comparison.hornSimplexFaceMap
#print axioms SerrePositivity.KST.Comparison.hornSimplexFaceMap

#check @SerrePositivity.KST.Comparison.hornFacesExUnit
#print axioms SerrePositivity.KST.Comparison.hornFacesExUnit

#check @SerrePositivity.KST.Comparison.hornSubdivisionComparison
#print axioms SerrePositivity.KST.Comparison.hornSubdivisionComparison


-- HornSubdivisionFaceMaps.lean

#check @SerrePositivity.KST.Comparison.hornSubdivisionFaceMap
#print axioms SerrePositivity.KST.Comparison.hornSubdivisionFaceMap

#check @SerrePositivity.KST.Comparison.hornSubdivisionFaceMap_ambient
#print axioms SerrePositivity.KST.Comparison.hornSubdivisionFaceMap_ambient

#check @SerrePositivity.KST.Comparison.hornSubdivisionNerveFaceCover
#print axioms SerrePositivity.KST.Comparison.hornSubdivisionNerveFaceCover

#check @SerrePositivity.KST.Comparison.hornSubdivisionFaceMap_common
#print axioms SerrePositivity.KST.Comparison.hornSubdivisionFaceMap_common


-- HornSubdivisionInclusion.lean

#check @SerrePositivity.KST.Comparison.hornSimplex_yoneda_inclusion
#print axioms SerrePositivity.KST.Comparison.hornSimplex_yoneda_inclusion

#check @SerrePositivity.KST.Comparison.hornSubdivisionComparison_inclusion
#print axioms SerrePositivity.KST.Comparison.hornSubdivisionComparison_inclusion


-- HornSubdivisionIso.lean

#check @SerrePositivity.KST.Comparison.hornSubdivisionComparison_app_injective
#print axioms SerrePositivity.KST.Comparison.hornSubdivisionComparison_app_injective

#check @SerrePositivity.KST.Comparison.hornSubdivisionComparison_isIso
#print axioms SerrePositivity.KST.Comparison.hornSubdivisionComparison_isIso


-- HornSubdivisionLastVertex.lean

#check @SerrePositivity.KST.Comparison.hornFacesExUnit_lastVertex
#print axioms SerrePositivity.KST.Comparison.hornFacesExUnit_lastVertex

#check @SerrePositivity.KST.Comparison.hornSubdivisionComparison_lastVertex
#print axioms SerrePositivity.KST.Comparison.hornSubdivisionComparison_lastVertex


-- HornSubdivisionSurjective.lean

#check @SerrePositivity.KST.Comparison.hornFaceInclusion_nerve_app_injective
#print axioms SerrePositivity.KST.Comparison.hornFaceInclusion_nerve_app_injective

#check @SerrePositivity.KST.Comparison.hornSubdivisionComparison_face
#print axioms SerrePositivity.KST.Comparison.hornSubdivisionComparison_face

#check @SerrePositivity.KST.Comparison.hornSubdivisionComparison_app_surjective
#print axioms SerrePositivity.KST.Comparison.hornSubdivisionComparison_app_surjective

#check @SerrePositivity.KST.Comparison.hornSubdivisionComparison_epi
#print axioms SerrePositivity.KST.Comparison.hornSubdivisionComparison_epi


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


-- LocalizedCoproductMaps.lean

#check @SerrePositivity.KST.Comparison.coprodMap_left_localized_isIso
#print axioms SerrePositivity.KST.Comparison.coprodMap_left_localized_isIso

#check @SerrePositivity.KST.Comparison.coprodMap_right_localized_isIso
#print axioms SerrePositivity.KST.Comparison.coprodMap_right_localized_isIso

#check @SerrePositivity.KST.Comparison.coprodMap_localized_isIso
#print axioms SerrePositivity.KST.Comparison.coprodMap_localized_isIso


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


-- NerveChainsLastVertex.lean

#check @SerrePositivity.KST.Comparison.nerveChainsExUnit_lastVertex
#print axioms SerrePositivity.KST.Comparison.nerveChainsExUnit_lastVertex

#check @SerrePositivity.KST.Comparison.subdivisionNerveChains_naturality
#print axioms SerrePositivity.KST.Comparison.subdivisionNerveChains_naturality

#check @SerrePositivity.KST.Comparison.subdivisionNerveChains_lastVertex
#print axioms SerrePositivity.KST.Comparison.subdivisionNerveChains_lastVertex


-- OrderNerveContraction.lean

#check @SerrePositivity.KST.Comparison.orderNerveSubcomplex
#print axioms SerrePositivity.KST.Comparison.orderNerveSubcomplex

#check @SerrePositivity.KST.Comparison.orderIntervalMap
#print axioms SerrePositivity.KST.Comparison.orderIntervalMap

#check @SerrePositivity.KST.Comparison.orderNerveHomotopyMap
#print axioms SerrePositivity.KST.Comparison.orderNerveHomotopyMap

#check @SerrePositivity.KST.Comparison.orderNerveHomotopyMap_zero
#print axioms SerrePositivity.KST.Comparison.orderNerveHomotopyMap_zero

#check @SerrePositivity.KST.Comparison.orderNerveHomotopyMap_one
#print axioms SerrePositivity.KST.Comparison.orderNerveHomotopyMap_one

#check @SerrePositivity.KST.Comparison.orderNerveHomotopyMap_mem
#print axioms SerrePositivity.KST.Comparison.orderNerveHomotopyMap_mem

#check @SerrePositivity.KST.Comparison.orderNerveSubcomplex_anodyne
#print axioms SerrePositivity.KST.Comparison.orderNerveSubcomplex_anodyne


-- OrderNerveSubcomplexIso.lean

#check @SerrePositivity.KST.Comparison.orderSubtypeInclusion
#print axioms SerrePositivity.KST.Comparison.orderSubtypeInclusion

#check @SerrePositivity.KST.Comparison.orderNerveSubcomplexIso
#print axioms SerrePositivity.KST.Comparison.orderNerveSubcomplexIso

#check @SerrePositivity.KST.Comparison.orderNerveSubcomplexIso_inclusion
#print axioms SerrePositivity.KST.Comparison.orderNerveSubcomplexIso_inclusion

#check @SerrePositivity.KST.Comparison.orderSubtypeNerve_anodyne
#print axioms SerrePositivity.KST.Comparison.orderSubtypeNerve_anodyne


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


-- RegularBarLoop.lean

#check @SerrePositivity.KST.Comparison.regularActionInterval_projection
#print axioms SerrePositivity.KST.Comparison.regularActionInterval_projection

#check @SerrePositivity.KST.Comparison.regularBarContraction_projection
#print axioms SerrePositivity.KST.Comparison.regularBarContraction_projection


-- RegularBarProjection.lean

#check @SerrePositivity.KST.Comparison.regularBarProjection
#print axioms SerrePositivity.KST.Comparison.regularBarProjection

#check @SerrePositivity.KST.Comparison.regularBarFiberMap
#print axioms SerrePositivity.KST.Comparison.regularBarFiberMap

#check @SerrePositivity.KST.Comparison.regularBarFiberMap_projection
#print axioms SerrePositivity.KST.Comparison.regularBarFiberMap_projection


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


-- SequenceHomotopyPullbacks.lean

#check @SerrePositivity.KST.Comparison.diagramArrow_id_homotopyPullback
#print axioms SerrePositivity.KST.Comparison.diagramArrow_id_homotopyPullback

#check @SerrePositivity.KST.Comparison.sequenceArrow_homotopyPullback_of_successors
#print axioms SerrePositivity.KST.Comparison.sequenceArrow_homotopyPullback_of_successors


-- SimplexComponents.lean

#check @SerrePositivity.KST.Comparison.simplexVertex
#print axioms SerrePositivity.KST.Comparison.simplexVertex

#check @SerrePositivity.KST.Comparison.simplexVertex_class_eq
#print axioms SerrePositivity.KST.Comparison.simplexVertex_class_eq

#check @SerrePositivity.KST.Comparison.simplexClass
#print axioms SerrePositivity.KST.Comparison.simplexClass

#check @SerrePositivity.KST.Comparison.simplexClass_map
#print axioms SerrePositivity.KST.Comparison.simplexClass_map

#check @SerrePositivity.KST.Comparison.simplexClass_zero
#print axioms SerrePositivity.KST.Comparison.simplexClass_zero


-- SimplexContraction.lean

#check @SerrePositivity.KST.Comparison.simplexContractionAt
#print axioms SerrePositivity.KST.Comparison.simplexContractionAt

#check @SerrePositivity.KST.Comparison.simplexContractionMap
#print axioms SerrePositivity.KST.Comparison.simplexContractionMap

#check @SerrePositivity.KST.Comparison.simplexContraction
#print axioms SerrePositivity.KST.Comparison.simplexContraction

#check @SerrePositivity.KST.Comparison.simplexMapContraction
#print axioms SerrePositivity.KST.Comparison.simplexMapContraction


-- SimplexFaceRetraction.lean

#check @SerrePositivity.KST.Comparison.simplexFaceRetraction
#print axioms SerrePositivity.KST.Comparison.simplexFaceRetraction

#check @SerrePositivity.KST.Comparison.simplexFaceRetraction_section
#print axioms SerrePositivity.KST.Comparison.simplexFaceRetraction_section

#check @SerrePositivity.KST.Comparison.simplexFaceRetraction_recover
#print axioms SerrePositivity.KST.Comparison.simplexFaceRetraction_recover

#check @SerrePositivity.KST.Comparison.simplexFaceRetraction_chain
#print axioms SerrePositivity.KST.Comparison.simplexFaceRetraction_chain


-- SimplicialCoproductMono.lean

#check @SerrePositivity.KST.Comparison.simplicialMonoCoprod
#print axioms SerrePositivity.KST.Comparison.simplicialMonoCoprod


-- SimplicialMonoidInternal.lean

#check @SerrePositivity.KST.Comparison.simplicialMonoidToInternal
#print axioms SerrePositivity.KST.Comparison.simplicialMonoidToInternal

#check @SerrePositivity.KST.Comparison.internalMonoidToSimplicial
#print axioms SerrePositivity.KST.Comparison.internalMonoidToSimplicial

#check @SerrePositivity.KST.Comparison.simplicialMonoidToInternal_space
#print axioms SerrePositivity.KST.Comparison.simplicialMonoidToInternal_space

#check @SerrePositivity.KST.Comparison.internalMonoidToSimplicial_space
#print axioms SerrePositivity.KST.Comparison.internalMonoidToSimplicial_space


-- SimplicialSum.lean

#check @SerrePositivity.KST.Comparison.simplicialSum
#print axioms SerrePositivity.KST.Comparison.simplicialSum

#check @SerrePositivity.KST.Comparison.simplicialSumInclusion
#print axioms SerrePositivity.KST.Comparison.simplicialSumInclusion

#check @SerrePositivity.KST.Comparison.simplicialSumDesc
#print axioms SerrePositivity.KST.Comparison.simplicialSumDesc

#check @SerrePositivity.KST.Comparison.simplicialSumInclusion_desc
#print axioms SerrePositivity.KST.Comparison.simplicialSumInclusion_desc

#check @SerrePositivity.KST.Comparison.simplicialSum_hom_ext
#print axioms SerrePositivity.KST.Comparison.simplicialSum_hom_ext

#check @SerrePositivity.KST.Comparison.simplicialSumIsCoproduct
#print axioms SerrePositivity.KST.Comparison.simplicialSumIsCoproduct

#check @SerrePositivity.KST.Comparison.simplicialSumMap
#print axioms SerrePositivity.KST.Comparison.simplicialSumMap

#check @SerrePositivity.KST.Comparison.simplicialSumInclusion_map
#print axioms SerrePositivity.KST.Comparison.simplicialSumInclusion_map


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

#check @SerrePositivity.KST.Comparison.simplicialSumReindex
#print axioms SerrePositivity.KST.Comparison.simplicialSumReindex

#check @SerrePositivity.KST.Comparison.simplicialSumInclusion_reindex
#print axioms SerrePositivity.KST.Comparison.simplicialSumInclusion_reindex

#check @SerrePositivity.KST.Comparison.simplicialSumReindex_commSq
#print axioms SerrePositivity.KST.Comparison.simplicialSumReindex_commSq

#check @SerrePositivity.KST.Comparison.simplicialSumReindex_isPullback
#print axioms SerrePositivity.KST.Comparison.simplicialSumReindex_isPullback

#check @SerrePositivity.KST.Comparison.simplicialSumInclusion_isPullback
#print axioms SerrePositivity.KST.Comparison.simplicialSumInclusion_isPullback


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


-- SpanStrictification.lean

#check @SerrePositivity.KST.Comparison.spanStrictification_of_mono
#print axioms SerrePositivity.KST.Comparison.spanStrictification_of_mono


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


-- SubdivisionAdjunctionSimplex.lean

#check @SerrePositivity.KST.Comparison.subdivisionHomEquiv_app_down
#print axioms SerrePositivity.KST.Comparison.subdivisionHomEquiv_app_down


-- SubdivisionAnodyne.lean

#check @SerrePositivity.KST.Comparison.subdivisionHorn_anodyne
#print axioms SerrePositivity.KST.Comparison.subdivisionHorn_anodyne

#check @SerrePositivity.KST.Comparison.ex_map_rlp
#print axioms SerrePositivity.KST.Comparison.ex_map_rlp

#check @SerrePositivity.KST.Comparison.subdivision_map_anodyne
#print axioms SerrePositivity.KST.Comparison.subdivision_map_anodyne


-- SubdivisionCommonFace.lean

#check @SerrePositivity.KST.Comparison.subdivisionCommonFace
#print axioms SerrePositivity.KST.Comparison.subdivisionCommonFace


-- SubdivisionCommutation.lean

#check @SerrePositivity.KST.Comparison.liftedDegeneracy_le_iff_of_ne
#print axioms SerrePositivity.KST.Comparison.liftedDegeneracy_le_iff_of_ne

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_cut
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_cut

#check @SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_cut
#print axioms SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_cut

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_cut_lt
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_cut_lt

#check @SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_cut_lt
#print axioms SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_cut_lt


-- SubdivisionCut.lean

#check @SerrePositivity.KST.Comparison.finiteChain_le_initialSegment
#print axioms SerrePositivity.KST.Comparison.finiteChain_le_initialSegment

#check @SerrePositivity.KST.Comparison.finiteChainCut
#print axioms SerrePositivity.KST.Comparison.finiteChainCut

#check @SerrePositivity.KST.Comparison.finiteChainCut_maximum
#print axioms SerrePositivity.KST.Comparison.finiteChainCut_maximum

#check @SerrePositivity.KST.Comparison.finiteChainCut_comp
#print axioms SerrePositivity.KST.Comparison.finiteChainCut_comp

#check @SerrePositivity.KST.Comparison.finiteChainCut_idempotent
#print axioms SerrePositivity.KST.Comparison.finiteChainCut_idempotent

#check @SerrePositivity.KST.Comparison.finiteChainCut_last
#print axioms SerrePositivity.KST.Comparison.finiteChainCut_last

#check @SerrePositivity.KST.Comparison.finiteChainCut_zero
#print axioms SerrePositivity.KST.Comparison.finiteChainCut_zero

#check @SerrePositivity.KST.Comparison.subdivisionCutAt
#print axioms SerrePositivity.KST.Comparison.subdivisionCutAt

#check @SerrePositivity.KST.Comparison.subdivisionCutAt_comp
#print axioms SerrePositivity.KST.Comparison.subdivisionCutAt_comp

#check @SerrePositivity.KST.Comparison.subdivisionCutAt_idempotent
#print axioms SerrePositivity.KST.Comparison.subdivisionCutAt_idempotent

#check @SerrePositivity.KST.Comparison.subdivisionCutAt_last
#print axioms SerrePositivity.KST.Comparison.subdivisionCutAt_last

#check @SerrePositivity.KST.Comparison.subdivisionCutAt_zero
#print axioms SerrePositivity.KST.Comparison.subdivisionCutAt_zero

#check @SerrePositivity.KST.Comparison.subdivisionCutAt_lastVertex
#print axioms SerrePositivity.KST.Comparison.subdivisionCutAt_lastVertex


-- SubdivisionDegeneracy.lean

#check @SerrePositivity.KST.Comparison.liftedDegeneracy
#print axioms SerrePositivity.KST.Comparison.liftedDegeneracy

#check @SerrePositivity.KST.Comparison.liftedFace
#print axioms SerrePositivity.KST.Comparison.liftedFace

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy

#check @SerrePositivity.KST.Comparison.liftedFace_image_not_mem
#print axioms SerrePositivity.KST.Comparison.liftedFace_image_not_mem

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_face
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_face

#check @SerrePositivity.KST.Comparison.subdivisionDegeneracyAt
#print axioms SerrePositivity.KST.Comparison.subdivisionDegeneracyAt

#check @SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_face
#print axioms SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_face


-- SubdivisionDoubleDegeneracy.lean

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_double
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_double

#check @SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_double
#print axioms SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_double

#check @SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_double_cut
#print axioms SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_double_cut


-- SubdivisionFaceCut.lean

#check @SerrePositivity.KST.Comparison.finiteChainCut_map_absorb
#print axioms SerrePositivity.KST.Comparison.finiteChainCut_map_absorb

#check @SerrePositivity.KST.Comparison.liftedFace_above
#print axioms SerrePositivity.KST.Comparison.liftedFace_above

#check @SerrePositivity.KST.Comparison.subdivisionCutAt_face_absorb
#print axioms SerrePositivity.KST.Comparison.subdivisionCutAt_face_absorb


-- SubdivisionFaceDegeneracy.lean

#check @SerrePositivity.KST.Comparison.liftedFace_special
#print axioms SerrePositivity.KST.Comparison.liftedFace_special

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_face_right
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_face_right

#check @SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_face_right
#print axioms SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_face_right


-- SubdivisionFaceLifting.lean

#check @SerrePositivity.KST.Comparison.simplexHom_factor_face
#print axioms SerrePositivity.KST.Comparison.simplexHom_factor_face

#check @SerrePositivity.KST.Comparison.subdivisionFace_app_injective
#print axioms SerrePositivity.KST.Comparison.subdivisionFace_app_injective

#check @SerrePositivity.KST.Comparison.subdivisionFace_avoids
#print axioms SerrePositivity.KST.Comparison.subdivisionFace_avoids

#check @SerrePositivity.KST.Comparison.subdivisionFace_lift
#print axioms SerrePositivity.KST.Comparison.subdivisionFace_lift


-- SubdivisionFrontCut.lean

#check @SerrePositivity.KST.Comparison.liftedFace_front_above
#print axioms SerrePositivity.KST.Comparison.liftedFace_front_above

#check @SerrePositivity.KST.Comparison.subdivisionCutAt_front_face_absorb
#print axioms SerrePositivity.KST.Comparison.subdivisionCutAt_front_face_absorb


-- SubdivisionFrontDegeneracy.lean

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_front
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_front

#check @SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_front
#print axioms SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_front


-- SubdivisionFrontFace.lean

#check @SerrePositivity.KST.Comparison.finiteChainFrontImage
#print axioms SerrePositivity.KST.Comparison.finiteChainFrontImage

#check @SerrePositivity.KST.Comparison.finiteChainFrontImage_maximum
#print axioms SerrePositivity.KST.Comparison.finiteChainFrontImage_maximum

#check @SerrePositivity.KST.Comparison.finiteChainFrontImage_singleton_ge
#print axioms SerrePositivity.KST.Comparison.finiteChainFrontImage_singleton_ge

#check @SerrePositivity.KST.Comparison.finiteChainFrontImage_of_max_ge
#print axioms SerrePositivity.KST.Comparison.finiteChainFrontImage_of_max_ge

#check @SerrePositivity.KST.Comparison.finiteChainFrontImage_absorb
#print axioms SerrePositivity.KST.Comparison.finiteChainFrontImage_absorb

#check @SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_front_absorb
#print axioms SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_front_absorb


-- SubdivisionIntervals.lean

#check @SerrePositivity.KST.Comparison.finiteChainCut_initialSegment
#print axioms SerrePositivity.KST.Comparison.finiteChainCut_initialSegment

#check @SerrePositivity.KST.Comparison.finiteChainCut_singleton
#print axioms SerrePositivity.KST.Comparison.finiteChainCut_singleton

#check @SerrePositivity.KST.Comparison.liftedDegeneracy_succ
#print axioms SerrePositivity.KST.Comparison.liftedDegeneracy_succ

#check @SerrePositivity.KST.Comparison.liftedDegeneracy_surjective
#print axioms SerrePositivity.KST.Comparison.liftedDegeneracy_surjective

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_initialSegment
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_initialSegment

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_singleton
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_singleton


-- SubdivisionLastVertex.lean

#check @SerrePositivity.KST.Comparison.finiteChainMaximum
#print axioms SerrePositivity.KST.Comparison.finiteChainMaximum

#check @SerrePositivity.KST.Comparison.finiteChainMaximum_map
#print axioms SerrePositivity.KST.Comparison.finiteChainMaximum_map

#check @SerrePositivity.KST.Comparison.subdivisionLastVertexAt
#print axioms SerrePositivity.KST.Comparison.subdivisionLastVertexAt

#check @SerrePositivity.KST.Comparison.subdivisionLastVertex_naturality
#print axioms SerrePositivity.KST.Comparison.subdivisionLastVertex_naturality

#check @SerrePositivity.KST.Comparison.subdivisionLastVertex
#print axioms SerrePositivity.KST.Comparison.subdivisionLastVertex

#check @SerrePositivity.KST.Comparison.finiteChainInitialSegment
#print axioms SerrePositivity.KST.Comparison.finiteChainInitialSegment

#check @SerrePositivity.KST.Comparison.finiteChainMaximum_initialSegment
#print axioms SerrePositivity.KST.Comparison.finiteChainMaximum_initialSegment

#check @SerrePositivity.KST.Comparison.subdivisionVertexSectionAt
#print axioms SerrePositivity.KST.Comparison.subdivisionVertexSectionAt

#check @SerrePositivity.KST.Comparison.subdivisionVertexSectionAt_lastVertex
#print axioms SerrePositivity.KST.Comparison.subdivisionVertexSectionAt_lastVertex

#check @SerrePositivity.KST.Comparison.subdivisionLastVertexAt_epi
#print axioms SerrePositivity.KST.Comparison.subdivisionLastVertexAt_epi


-- SubdivisionLastVertexMap.lean

#check @SerrePositivity.KST.Comparison.subdivisionLastVertexMap
#print axioms SerrePositivity.KST.Comparison.subdivisionLastVertexMap


-- SubdivisionLastVertexSimplex.lean

#check @SerrePositivity.KST.Comparison.subdivisionLastVertexMap_on_simplex
#print axioms SerrePositivity.KST.Comparison.subdivisionLastVertexMap_on_simplex

#check @SerrePositivity.KST.Comparison.subdivisionLastVertexMap_stdSimplex
#print axioms SerrePositivity.KST.Comparison.subdivisionLastVertexMap_stdSimplex


-- SubdivisionMaximum.lean

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_maximum
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_maximum

#check @SerrePositivity.KST.Comparison.liftedDegeneracy_face_ge
#print axioms SerrePositivity.KST.Comparison.liftedDegeneracy_face_ge


-- SubdivisionNerveChains.lean

#check @SerrePositivity.KST.Comparison.nerveSimplexOrderHom
#print axioms SerrePositivity.KST.Comparison.nerveSimplexOrderHom

#check @SerrePositivity.KST.Comparison.finiteChainMap_comp
#print axioms SerrePositivity.KST.Comparison.finiteChainMap_comp

#check @SerrePositivity.KST.Comparison.nerveChainsExUnit
#print axioms SerrePositivity.KST.Comparison.nerveChainsExUnit

#check @SerrePositivity.KST.Comparison.subdivisionNerveChains
#print axioms SerrePositivity.KST.Comparison.subdivisionNerveChains

#check @SerrePositivity.KST.Comparison.nerveChainsExUnit_naturality
#print axioms SerrePositivity.KST.Comparison.nerveChainsExUnit_naturality


-- SubdivisionRearDegeneracy.lean

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_rear
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_rear

#check @SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_rear
#print axioms SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_rear


-- SubdivisionSimplexCover.lean

#check @SerrePositivity.KST.Comparison.subdivisionSimplexCover
#print axioms SerrePositivity.KST.Comparison.subdivisionSimplexCover


-- SubdivisionUnions.lean

#check @SerrePositivity.KST.Comparison.finiteChainCut_mem_iff
#print axioms SerrePositivity.KST.Comparison.finiteChainCut_mem_iff

#check @SerrePositivity.KST.Comparison.finiteChainCut_preservesUnion
#print axioms SerrePositivity.KST.Comparison.finiteChainCut_preservesUnion

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_mem_iff
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_mem_iff

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_preservesUnion
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_preservesUnion


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


-- TensorHomotopyPullbacks.lean

#check @SerrePositivity.KST.Comparison.tensorRight_isPullback
#print axioms SerrePositivity.KST.Comparison.tensorRight_isPullback

#check @SerrePositivity.KST.Comparison.isHomotopyPullback_tensorRight
#print axioms SerrePositivity.KST.Comparison.isHomotopyPullback_tensorRight


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


-- UniqueFaceNondegenerate.lean

#check @SerrePositivity.KST.Comparison.nonDegenerate_of_unique_face
#print axioms SerrePositivity.KST.Comparison.nonDegenerate_of_unique_face
