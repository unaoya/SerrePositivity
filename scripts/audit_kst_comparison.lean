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


-- CutDegeneracy.lean

#check @SerrePositivity.KST.Comparison.finiteChainCutDegeneracy_singleton
#print axioms SerrePositivity.KST.Comparison.finiteChainCutDegeneracy_singleton

#check @SerrePositivity.KST.Comparison.liftedDegeneracy_le_castSucc_iff
#print axioms SerrePositivity.KST.Comparison.liftedDegeneracy_le_castSucc_iff

#check @SerrePositivity.KST.Comparison.liftedDegeneracy_le_succ_iff
#print axioms SerrePositivity.KST.Comparison.liftedDegeneracy_le_succ_iff


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


-- ExDoublePairing.lean

#check @SerrePositivity.KST.Comparison.exPairingStep_double
#print axioms SerrePositivity.KST.Comparison.exPairingStep_double

#check @SerrePositivity.KST.Comparison.exPairingStep_double_degenerate
#print axioms SerrePositivity.KST.Comparison.exPairingStep_double_degenerate

#check @SerrePositivity.KST.Comparison.exPairingStep_notMem_range_of_nonDegenerate
#print axioms SerrePositivity.KST.Comparison.exPairingStep_notMem_range_of_nonDegenerate


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

#check @SerrePositivity.KST.Comparison.pullbackMapBase_localized_isIso_of_kan_base
#print axioms SerrePositivity.KST.Comparison.pullbackMapBase_localized_isIso_of_kan_base


-- FibrantTargetLifting.lean

#check @SerrePositivity.KST.Comparison.localizedMono_lifting_fibrantTarget
#print axioms SerrePositivity.KST.Comparison.localizedMono_lifting_fibrantTarget


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

#check @SerrePositivity.KST.Comparison.homotopyPullbackMap_localized_isIso_fixed_kan_base
#print axioms SerrePositivity.KST.Comparison.homotopyPullbackMap_localized_isIso_fixed_kan_base


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


-- HornPreimage.lean

#check @SerrePositivity.KST.Comparison.const_horn_vertex_mem
#print axioms SerrePositivity.KST.Comparison.const_horn_vertex_mem

#check @SerrePositivity.KST.Comparison.horn_preimage_localized_isIso
#print axioms SerrePositivity.KST.Comparison.horn_preimage_localized_isIso

#check @SerrePositivity.KST.Comparison.subcomplexPreimage_isPullback
#print axioms SerrePositivity.KST.Comparison.subcomplexPreimage_isPullback

#check @SerrePositivity.KST.Comparison.pullback_horn_localized_isIso
#print axioms SerrePositivity.KST.Comparison.pullback_horn_localized_isIso


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

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_horn_localized_isIso
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_horn_localized_isIso

#check @SerrePositivity.KST.Comparison.sliceFiberRightAdjoint_test_rlp
#print axioms SerrePositivity.KST.Comparison.sliceFiberRightAdjoint_test_rlp

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_anodyne_localized_isIso
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_anodyne_localized_isIso

#check @SerrePositivity.KST.Comparison.pullback_anodyne_localized_isIso
#print axioms SerrePositivity.KST.Comparison.pullback_anodyne_localized_isIso


-- KanBasePullback.lean

#check @SerrePositivity.KST.Comparison.sliceFiberRightAdjoint_kan
#print axioms SerrePositivity.KST.Comparison.sliceFiberRightAdjoint_kan

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_localizedMono_isIso
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_localizedMono_isIso

#check @SerrePositivity.KST.Comparison.sliceFiberFunctor_localized_isIso
#print axioms SerrePositivity.KST.Comparison.sliceFiberFunctor_localized_isIso

#check @SerrePositivity.KST.Comparison.pullback_localized_isIso_of_kan_base
#print axioms SerrePositivity.KST.Comparison.pullback_localized_isIso_of_kan_base


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


-- OverHornLifting.lean

#check @SerrePositivity.KST.Comparison.hornOverMap
#print axioms SerrePositivity.KST.Comparison.hornOverMap

#check @SerrePositivity.KST.Comparison.over_lifting_of_underlying
#print axioms SerrePositivity.KST.Comparison.over_lifting_of_underlying

#check @SerrePositivity.KST.Comparison.underlying_rlp_of_over_horns
#print axioms SerrePositivity.KST.Comparison.underlying_rlp_of_over_horns


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


-- SubcomplexContraction.lean

#check @SerrePositivity.KST.Comparison.localized_interval_endpoints
#print axioms SerrePositivity.KST.Comparison.localized_interval_endpoints

#check @SerrePositivity.KST.Comparison.subcomplex_inclusion_localized_isIso
#print axioms SerrePositivity.KST.Comparison.subcomplex_inclusion_localized_isIso


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


-- SubdivisionMaximum.lean

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_maximum
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_maximum

#check @SerrePositivity.KST.Comparison.liftedDegeneracy_face_ge
#print axioms SerrePositivity.KST.Comparison.liftedDegeneracy_face_ge


-- SubdivisionRearDegeneracy.lean

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_rear
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_rear

#check @SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_rear
#print axioms SerrePositivity.KST.Comparison.subdivisionDegeneracyAt_rear


-- SubdivisionUnions.lean

#check @SerrePositivity.KST.Comparison.finiteChainCut_mem_iff
#print axioms SerrePositivity.KST.Comparison.finiteChainCut_mem_iff

#check @SerrePositivity.KST.Comparison.finiteChainCut_preservesUnion
#print axioms SerrePositivity.KST.Comparison.finiteChainCut_preservesUnion

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_mem_iff
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_mem_iff

#check @SerrePositivity.KST.Comparison.finiteChainDegeneracy_preservesUnion
#print axioms SerrePositivity.KST.Comparison.finiteChainDegeneracy_preservesUnion


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
