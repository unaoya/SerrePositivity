import SerrePositivity.InfinityCategories.Core
import SerrePositivity.InfinityCategories.Core.LeftFiberKan
import SerrePositivity.InfinityCategories.Core.PrismVerticalSimplex
import SerrePositivity.InfinityCategories.Core.VertexFiberNervePullback
import SerrePositivity.InfinityCategories.F1.CocartesianCrossingComparison
import SerrePositivity.InfinityCategories.F1.CosliceFiberCoordinates
import SerrePositivity.InfinityCategories.F1.CosliceFiberDiagramChange
import SerrePositivity.InfinityCategories.F1.CosliceFiberPostcomposition
import SerrePositivity.InfinityCategories.F1.CosliceFiberUniversal
import SerrePositivity.InfinityCategories.F1.CosliceIntervalNaturality
import SerrePositivity.InfinityCategories.F1.CoslicePinchedIso
import SerrePositivity.InfinityCategories.F1.InnerAnodynePrismExtension
import SerrePositivity.InfinityCategories.F1.IntervalComparisonMono
import SerrePositivity.InfinityCategories.F1.IntervalPrismHomotopy
import SerrePositivity.InfinityCategories.F1.LeftIntervalEquivalence
import SerrePositivity.InfinityCategories.F1.LeftIntervalFatDiagram
import SerrePositivity.InfinityCategories.F1.LeftIntervalFatHomotopy
import SerrePositivity.InfinityCategories.F1.LeftIntervalFatNaturality
import SerrePositivity.InfinityCategories.F1.LeftIntervalHomotopySection
import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberIso
import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberKan
import SerrePositivity.InfinityCategories.F1.MappingCylinderGeneralComparison
import SerrePositivity.InfinityCategories.F1.MappingCylinderIntervalEquivalence
import SerrePositivity.InfinityCategories.F1.MappingCylinderQuasicategoryComparison
import SerrePositivity.InfinityCategories.F1.MappingSpaceIntervalComparison
import SerrePositivity.InfinityCategories.F1.RelativeFunctorEvaluation
import SerrePositivity.InfinityCategories.F1.RelativeFunctorSpace
import SerrePositivity.InfinityCategories.F1.RelativeFunctorVertices
import SerrePositivity.InfinityCategories.F1.RelativeJoinCocartesianFibration
import SerrePositivity.InfinityCategories.F1.RelativeJoinCrossingCocartesian
import SerrePositivity.InfinityCategories.F1.RelativeJoinExtensionEquivalence
import SerrePositivity.InfinityCategories.F1.RightIntervalEquivalence
import SerrePositivity.InfinityCategories.F1B.ScaffoldUnderChain
import Lean.Util.CollectAxioms

/-!
概要：直接置換後の原本の公開名・型と標準三公理を監査する。
方針：移動・重複除去の対象を #check し、各公開宣言の公理を再帰的に検査する。
規約：互換シムや旧名前空間に依存せず、既存の数学的宣言を参照する。
使われ方：R レーンの第 0〜1 段・第 5 段の回帰監査。
-/

#check @SerrePositivity.InfinityCategories.cocartesian_crossing_mapping_equivalence_of_target
#check @SerrePositivity.InfinityCategories.const_point_comp_yoneda
#check @SerrePositivity.InfinityCategories.constant_opObjEquiv
#check @SerrePositivity.InfinityCategories.cosliceFiberCurry
#check @SerrePositivity.InfinityCategories.cosliceFiberCurry_uncurry
#check @SerrePositivity.InfinityCategories.cosliceFiberDiagramIso
#check @SerrePositivity.InfinityCategories.cosliceFiberDiagramIso_uncurry
#check @SerrePositivity.InfinityCategories.cosliceFiberHomEquiv
#check @SerrePositivity.InfinityCategories.cosliceFiberPinchedLeftIso
#check @SerrePositivity.InfinityCategories.cosliceFiberSimplex
#check @SerrePositivity.InfinityCategories.cosliceFiberSimplexEquiv
#check @SerrePositivity.InfinityCategories.cosliceFiberSimplexInverse
#check @SerrePositivity.InfinityCategories.cosliceFiberSimplex_naturality
#check @SerrePositivity.InfinityCategories.cosliceFiberSimplex_source
#check @SerrePositivity.InfinityCategories.cosliceFiberSimplex_target
#check @SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace
#check @SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace_exists_homotopy
#check @SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace_exists_homotopy_section
#check @SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace_exists_retraction
#check @SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace_mono
#check @SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace_postcomp_essentiallySurjective
#check @SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace_uncurry
#check @SerrePositivity.InfinityCategories.cosliceFiberUncurry
#check @SerrePositivity.InfinityCategories.cosliceFiberUncurry_curry
#check @SerrePositivity.InfinityCategories.cosliceFiberUncurry_injective
#check @SerrePositivity.InfinityCategories.cosliceFiberUncurry_inl
#check @SerrePositivity.InfinityCategories.cosliceFiberUncurry_inr
#check @SerrePositivity.InfinityCategories.cosliceFiberUncurry_precomp
#check @SerrePositivity.InfinityCategories.cosliceIntervalComparison_naturality
#check @SerrePositivity.InfinityCategories.coslicePostcompFiberMap
#check @SerrePositivity.InfinityCategories.coslicePostcompFiberMap_equivalence_iff_pinchedHomMap
#check @SerrePositivity.InfinityCategories.coslicePostcompFiberMap_restrict
#check @SerrePositivity.InfinityCategories.coslicePostcompFiberMap_source_equivalence_of_target
#check @SerrePositivity.InfinityCategories.coslicePostcompFiberMap_ι
#check @SerrePositivity.InfinityCategories.exists_pre_fatJoinComparison_right_relative_retraction
#check @SerrePositivity.InfinityCategories.exists_relativeFunctorVertex
#check @SerrePositivity.InfinityCategories.innerAnodyne_extend_prism_over_interval
#check @SerrePositivity.InfinityCategories.innerAnodyne_prism_vertical_isCocartesian
#check @SerrePositivity.InfinityCategories.intervalBoundaryDiagram_postcomp
#check @SerrePositivity.InfinityCategories.intervalMappingBoundary_diagram
#check @SerrePositivity.InfinityCategories.intervalMappingCurryOfEndpoints
#check @SerrePositivity.InfinityCategories.intervalMappingHomotopyOfLeftFatJoin
#check @SerrePositivity.InfinityCategories.intervalMappingHomotopyOfPrism
#check @SerrePositivity.InfinityCategories.intervalMappingUncurry_curryOfEndpoints
#check @SerrePositivity.InfinityCategories.intervalMappingUncurry_one
#check @SerrePositivity.InfinityCategories.intervalMappingUncurry_zero
#check @SerrePositivity.InfinityCategories.isFullyFaithful_over_interval_of_endpoint_fibers_of_cocartesian_lifts
#check @SerrePositivity.InfinityCategories.isQCatEquivalence_over_interval_of_endpoint_fibers_of_cocartesian_lifts
#check @SerrePositivity.InfinityCategories.joinStdSimplexIso_leftPoint_inl
#check @SerrePositivity.InfinityCategories.joinStdSimplexIso_leftPoint_inr
#check @SerrePositivity.InfinityCategories.kanComplex_of_leftHornFillers
#check @SerrePositivity.InfinityCategories.leftIntervalCylinderProjection
#check @SerrePositivity.InfinityCategories.leftIntervalCylinderProjection_naturality
#check @SerrePositivity.InfinityCategories.leftIntervalCylinderProjection_one
#check @SerrePositivity.InfinityCategories.leftIntervalCylinderProjection_section
#check @SerrePositivity.InfinityCategories.leftIntervalCylinderProjection_zero
#check @SerrePositivity.InfinityCategories.leftIntervalCylinderSection
#check @SerrePositivity.InfinityCategories.leftIntervalCylinderSection_projection
#check @SerrePositivity.InfinityCategories.leftIntervalFatDiagram
#check @SerrePositivity.InfinityCategories.leftIntervalFatDiagram_comparison
#check @SerrePositivity.InfinityCategories.leftIntervalFatDiagram_cylinder
#check @SerrePositivity.InfinityCategories.leftIntervalFatDiagram_inl
#check @SerrePositivity.InfinityCategories.leftIntervalFatDiagram_inr
#check @SerrePositivity.InfinityCategories.leftIntervalFatDiagram_precomp
#check @SerrePositivity.InfinityCategories.leftIntervalFatDiagram_recover
#check @SerrePositivity.InfinityCategories.leftIntervalFatPrism
#check @SerrePositivity.InfinityCategories.leftIntervalFatPrism_comparison
#check @SerrePositivity.InfinityCategories.leftIntervalFatPrism_one
#check @SerrePositivity.InfinityCategories.leftIntervalFatPrism_zero
#check @SerrePositivity.InfinityCategories.leftMappingSpacePrism_hom_ext
#check @SerrePositivity.InfinityCategories.leftPinchedSimplexEquiv
#check @SerrePositivity.InfinityCategories.leftPointStdSimplexIso
#check @SerrePositivity.InfinityCategories.leftPointStdSimplexIso_face_inv
#check @SerrePositivity.InfinityCategories.leftPointStdSimplexIso_first_inv
#check @SerrePositivity.InfinityCategories.leftPointStdSimplexIso_inv_naturality
#check @SerrePositivity.InfinityCategories.leftUnstraighteningFiberIso
#check @SerrePositivity.InfinityCategories.leftUnstraighteningFiber_kanComplex
#check @SerrePositivity.InfinityCategories.mappingCylinder_isPrecompositionEquivalence
#check @SerrePositivity.InfinityCategories.mappingCylinder_isPrecompositionEquivalence_of_quasicategories
#check @SerrePositivity.InfinityCategories.mappingCylinder_isPrecompositionEquivalence_of_quasicategory_factors
#check @SerrePositivity.InfinityCategories.nerveUnderMap
#check @SerrePositivity.InfinityCategories.nerveUnderMap_comp
#check @SerrePositivity.InfinityCategories.nerveUnderMap_id
#check @SerrePositivity.InfinityCategories.nerveUnderMap_projection
#check @SerrePositivity.InfinityCategories.pinchedHomLeftToIntervalMappingSpace
#check @SerrePositivity.InfinityCategories.pinchedHomLeftToIntervalMappingSpace_mono
#check @SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace
#check @SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_mono
#check @SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_naturality
#check @SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_uncurry
#check @SerrePositivity.InfinityCategories.pinchedInterval_comparison_eq
#check @SerrePositivity.InfinityCategories.pointCosliceFiberMap
#check @SerrePositivity.InfinityCategories.pointCosliceFiberMap_eq_postcomp
#check @SerrePositivity.InfinityCategories.pointCosliceFiberMap_equivalence_iff_pinchedHomMap
#check @SerrePositivity.InfinityCategories.pointCosliceFiberMap_uncurry
#check @SerrePositivity.InfinityCategories.pointedSpaceFiber_kanComplex
#check @SerrePositivity.InfinityCategories.prismVerticalSimplex
#check @SerrePositivity.InfinityCategories.prismVerticalSimplex_naturality
#check @SerrePositivity.InfinityCategories.relativeFunctorCurry
#check @SerrePositivity.InfinityCategories.relativeFunctorEvaluate
#check @SerrePositivity.InfinityCategories.relativeFunctorEvaluate_ι
#check @SerrePositivity.InfinityCategories.relativeFunctorOverFunctor
#check @SerrePositivity.InfinityCategories.relativeFunctorOverPre
#check @SerrePositivity.InfinityCategories.relativeFunctorOverPre_comp
#check @SerrePositivity.InfinityCategories.relativeFunctorOverPre_id
#check @SerrePositivity.InfinityCategories.relativeFunctorOverPre_vertex
#check @SerrePositivity.InfinityCategories.relativeFunctorOverPre_ι
#check @SerrePositivity.InfinityCategories.relativeFunctorSpace
#check @SerrePositivity.InfinityCategories.relativeFunctorUncurry
#check @SerrePositivity.InfinityCategories.relativeFunctorUncurry_curry
#check @SerrePositivity.InfinityCategories.relativeFunctorUncurry_injective
#check @SerrePositivity.InfinityCategories.relativeFunctorUncurry_projection
#check @SerrePositivity.InfinityCategories.relativeFunctorVertex
#check @SerrePositivity.InfinityCategories.relativeJoinPrism_vertical_isCocartesian
#check @SerrePositivity.InfinityCategories.relativeJoinProjection_cocartesianFibration
#check @SerrePositivity.InfinityCategories.relativeJoin_crossing_isCocartesian
#check @SerrePositivity.InfinityCategories.relativeJoin_extension_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.relativeJoin_extension_preserved_lift
#check @SerrePositivity.InfinityCategories.relativeJoin_vertex_inl_of_projection_zero
#check @SerrePositivity.InfinityCategories.rev_extend_rev
#check @SerrePositivity.InfinityCategories.rev_front
#check @SerrePositivity.InfinityCategories.rev_lastVertex
#check @SerrePositivity.InfinityCategories.rightMappingSpacePrism_hom_ext
#check @SerrePositivity.InfinityCategories.scaffoldInitialTransformation
#check @SerrePositivity.InfinityCategories.scaffoldUnderChain
#check @SerrePositivity.InfinityCategories.scaffoldUnderChain_projection
#check @SerrePositivity.InfinityCategories.scaffoldUnderChain_restriction
#check @SerrePositivity.InfinityCategories.scaffoldUnderChain_yoneda_projection
#check @SerrePositivity.InfinityCategories.scaffoldUnderChain_yoneda_restriction
#check @SerrePositivity.InfinityCategories.sliceOverOpIso
#check @SerrePositivity.InfinityCategories.sliceOverOpIso_projection
#check @SerrePositivity.InfinityCategories.vertexFiberNervePullbackIso
#check @SerrePositivity.InfinityCategories.vertexFiberNervePullbackIso_hom_ι
#check @SerrePositivity.InfinityCategories.vertexFiberPullbackIso
#check @SerrePositivity.InfinityCategories.vertexFiberPullbackIso_hom_ι
#check @SerrePositivity.InfinityCategories.vertexFiberTransport_ι
#check @SerrePositivity.InfinityCategories.vertexFiber_kanComplex_of_leftFibration

open Lean in
run_cmd do
  let names := #[
    ``SerrePositivity.InfinityCategories.cocartesian_crossing_mapping_equivalence_of_target,
    ``SerrePositivity.InfinityCategories.const_point_comp_yoneda,
    ``SerrePositivity.InfinityCategories.constant_opObjEquiv,
    ``SerrePositivity.InfinityCategories.cosliceFiberCurry,
    ``SerrePositivity.InfinityCategories.cosliceFiberCurry_uncurry,
    ``SerrePositivity.InfinityCategories.cosliceFiberDiagramIso,
    ``SerrePositivity.InfinityCategories.cosliceFiberDiagramIso_uncurry,
    ``SerrePositivity.InfinityCategories.cosliceFiberHomEquiv,
    ``SerrePositivity.InfinityCategories.cosliceFiberPinchedLeftIso,
    ``SerrePositivity.InfinityCategories.cosliceFiberSimplex,
    ``SerrePositivity.InfinityCategories.cosliceFiberSimplexEquiv,
    ``SerrePositivity.InfinityCategories.cosliceFiberSimplexInverse,
    ``SerrePositivity.InfinityCategories.cosliceFiberSimplex_naturality,
    ``SerrePositivity.InfinityCategories.cosliceFiberSimplex_source,
    ``SerrePositivity.InfinityCategories.cosliceFiberSimplex_target,
    ``SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace,
    ``SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace_exists_homotopy,
    ``SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace_exists_homotopy_section,
    ``SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace_exists_retraction,
    ``SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace_isQCatEquivalence,
    ``SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace_mono,
    ``SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace_postcomp_essentiallySurjective,
    ``SerrePositivity.InfinityCategories.cosliceFiberToIntervalMappingSpace_uncurry,
    ``SerrePositivity.InfinityCategories.cosliceFiberUncurry,
    ``SerrePositivity.InfinityCategories.cosliceFiberUncurry_curry,
    ``SerrePositivity.InfinityCategories.cosliceFiberUncurry_injective,
    ``SerrePositivity.InfinityCategories.cosliceFiberUncurry_inl,
    ``SerrePositivity.InfinityCategories.cosliceFiberUncurry_inr,
    ``SerrePositivity.InfinityCategories.cosliceFiberUncurry_precomp,
    ``SerrePositivity.InfinityCategories.cosliceIntervalComparison_naturality,
    ``SerrePositivity.InfinityCategories.coslicePostcompFiberMap,
    ``SerrePositivity.InfinityCategories.coslicePostcompFiberMap_equivalence_iff_pinchedHomMap,
    ``SerrePositivity.InfinityCategories.coslicePostcompFiberMap_restrict,
    ``SerrePositivity.InfinityCategories.coslicePostcompFiberMap_source_equivalence_of_target,
    ``SerrePositivity.InfinityCategories.coslicePostcompFiberMap_ι,
    ``SerrePositivity.InfinityCategories.exists_pre_fatJoinComparison_right_relative_retraction,
    ``SerrePositivity.InfinityCategories.exists_relativeFunctorVertex,
    ``SerrePositivity.InfinityCategories.innerAnodyne_extend_prism_over_interval,
    ``SerrePositivity.InfinityCategories.innerAnodyne_prism_vertical_isCocartesian,
    ``SerrePositivity.InfinityCategories.intervalBoundaryDiagram_postcomp,
    ``SerrePositivity.InfinityCategories.intervalMappingBoundary_diagram,
    ``SerrePositivity.InfinityCategories.intervalMappingCurryOfEndpoints,
    ``SerrePositivity.InfinityCategories.intervalMappingHomotopyOfLeftFatJoin,
    ``SerrePositivity.InfinityCategories.intervalMappingHomotopyOfPrism,
    ``SerrePositivity.InfinityCategories.intervalMappingUncurry_curryOfEndpoints,
    ``SerrePositivity.InfinityCategories.intervalMappingUncurry_one,
    ``SerrePositivity.InfinityCategories.intervalMappingUncurry_zero,
    ``SerrePositivity.InfinityCategories.isFullyFaithful_over_interval_of_endpoint_fibers_of_cocartesian_lifts,
    ``SerrePositivity.InfinityCategories.isQCatEquivalence_over_interval_of_endpoint_fibers_of_cocartesian_lifts,
    ``SerrePositivity.InfinityCategories.joinStdSimplexIso_leftPoint_inl,
    ``SerrePositivity.InfinityCategories.joinStdSimplexIso_leftPoint_inr,
    ``SerrePositivity.InfinityCategories.kanComplex_of_leftHornFillers,
    ``SerrePositivity.InfinityCategories.leftIntervalCylinderProjection,
    ``SerrePositivity.InfinityCategories.leftIntervalCylinderProjection_naturality,
    ``SerrePositivity.InfinityCategories.leftIntervalCylinderProjection_one,
    ``SerrePositivity.InfinityCategories.leftIntervalCylinderProjection_section,
    ``SerrePositivity.InfinityCategories.leftIntervalCylinderProjection_zero,
    ``SerrePositivity.InfinityCategories.leftIntervalCylinderSection,
    ``SerrePositivity.InfinityCategories.leftIntervalCylinderSection_projection,
    ``SerrePositivity.InfinityCategories.leftIntervalFatDiagram,
    ``SerrePositivity.InfinityCategories.leftIntervalFatDiagram_comparison,
    ``SerrePositivity.InfinityCategories.leftIntervalFatDiagram_cylinder,
    ``SerrePositivity.InfinityCategories.leftIntervalFatDiagram_inl,
    ``SerrePositivity.InfinityCategories.leftIntervalFatDiagram_inr,
    ``SerrePositivity.InfinityCategories.leftIntervalFatDiagram_precomp,
    ``SerrePositivity.InfinityCategories.leftIntervalFatDiagram_recover,
    ``SerrePositivity.InfinityCategories.leftIntervalFatPrism,
    ``SerrePositivity.InfinityCategories.leftIntervalFatPrism_comparison,
    ``SerrePositivity.InfinityCategories.leftIntervalFatPrism_one,
    ``SerrePositivity.InfinityCategories.leftIntervalFatPrism_zero,
    ``SerrePositivity.InfinityCategories.leftMappingSpacePrism_hom_ext,
    ``SerrePositivity.InfinityCategories.leftPinchedSimplexEquiv,
    ``SerrePositivity.InfinityCategories.leftPointStdSimplexIso,
    ``SerrePositivity.InfinityCategories.leftPointStdSimplexIso_face_inv,
    ``SerrePositivity.InfinityCategories.leftPointStdSimplexIso_first_inv,
    ``SerrePositivity.InfinityCategories.leftPointStdSimplexIso_inv_naturality,
    ``SerrePositivity.InfinityCategories.leftUnstraighteningFiberIso,
    ``SerrePositivity.InfinityCategories.leftUnstraighteningFiber_kanComplex,
    ``SerrePositivity.InfinityCategories.mappingCylinder_isPrecompositionEquivalence,
    ``SerrePositivity.InfinityCategories.mappingCylinder_isPrecompositionEquivalence_of_quasicategories,
    ``SerrePositivity.InfinityCategories.mappingCylinder_isPrecompositionEquivalence_of_quasicategory_factors,
    ``SerrePositivity.InfinityCategories.nerveUnderMap,
    ``SerrePositivity.InfinityCategories.nerveUnderMap_comp,
    ``SerrePositivity.InfinityCategories.nerveUnderMap_id,
    ``SerrePositivity.InfinityCategories.nerveUnderMap_projection,
    ``SerrePositivity.InfinityCategories.pinchedHomLeftToIntervalMappingSpace,
    ``SerrePositivity.InfinityCategories.pinchedHomLeftToIntervalMappingSpace_mono,
    ``SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace,
    ``SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence,
    ``SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_mono,
    ``SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_naturality,
    ``SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_uncurry,
    ``SerrePositivity.InfinityCategories.pinchedInterval_comparison_eq,
    ``SerrePositivity.InfinityCategories.pointCosliceFiberMap,
    ``SerrePositivity.InfinityCategories.pointCosliceFiberMap_eq_postcomp,
    ``SerrePositivity.InfinityCategories.pointCosliceFiberMap_equivalence_iff_pinchedHomMap,
    ``SerrePositivity.InfinityCategories.pointCosliceFiberMap_uncurry,
    ``SerrePositivity.InfinityCategories.pointedSpaceFiber_kanComplex,
    ``SerrePositivity.InfinityCategories.prismVerticalSimplex,
    ``SerrePositivity.InfinityCategories.prismVerticalSimplex_naturality,
    ``SerrePositivity.InfinityCategories.relativeFunctorCurry,
    ``SerrePositivity.InfinityCategories.relativeFunctorEvaluate,
    ``SerrePositivity.InfinityCategories.relativeFunctorEvaluate_ι,
    ``SerrePositivity.InfinityCategories.relativeFunctorOverFunctor,
    ``SerrePositivity.InfinityCategories.relativeFunctorOverPre,
    ``SerrePositivity.InfinityCategories.relativeFunctorOverPre_comp,
    ``SerrePositivity.InfinityCategories.relativeFunctorOverPre_id,
    ``SerrePositivity.InfinityCategories.relativeFunctorOverPre_vertex,
    ``SerrePositivity.InfinityCategories.relativeFunctorOverPre_ι,
    ``SerrePositivity.InfinityCategories.relativeFunctorSpace,
    ``SerrePositivity.InfinityCategories.relativeFunctorUncurry,
    ``SerrePositivity.InfinityCategories.relativeFunctorUncurry_curry,
    ``SerrePositivity.InfinityCategories.relativeFunctorUncurry_injective,
    ``SerrePositivity.InfinityCategories.relativeFunctorUncurry_projection,
    ``SerrePositivity.InfinityCategories.relativeFunctorVertex,
    ``SerrePositivity.InfinityCategories.relativeJoinPrism_vertical_isCocartesian,
    ``SerrePositivity.InfinityCategories.relativeJoinProjection_cocartesianFibration,
    ``SerrePositivity.InfinityCategories.relativeJoin_crossing_isCocartesian,
    ``SerrePositivity.InfinityCategories.relativeJoin_extension_isQCatEquivalence,
    ``SerrePositivity.InfinityCategories.relativeJoin_extension_preserved_lift,
    ``SerrePositivity.InfinityCategories.relativeJoin_vertex_inl_of_projection_zero,
    ``SerrePositivity.InfinityCategories.rev_extend_rev,
    ``SerrePositivity.InfinityCategories.rev_front,
    ``SerrePositivity.InfinityCategories.rev_lastVertex,
    ``SerrePositivity.InfinityCategories.rightMappingSpacePrism_hom_ext,
    ``SerrePositivity.InfinityCategories.scaffoldInitialTransformation,
    ``SerrePositivity.InfinityCategories.scaffoldUnderChain,
    ``SerrePositivity.InfinityCategories.scaffoldUnderChain_projection,
    ``SerrePositivity.InfinityCategories.scaffoldUnderChain_restriction,
    ``SerrePositivity.InfinityCategories.scaffoldUnderChain_yoneda_projection,
    ``SerrePositivity.InfinityCategories.scaffoldUnderChain_yoneda_restriction,
    ``SerrePositivity.InfinityCategories.sliceOverOpIso,
    ``SerrePositivity.InfinityCategories.sliceOverOpIso_projection,
    ``SerrePositivity.InfinityCategories.vertexFiberNervePullbackIso,
    ``SerrePositivity.InfinityCategories.vertexFiberNervePullbackIso_hom_ι,
    ``SerrePositivity.InfinityCategories.vertexFiberPullbackIso,
    ``SerrePositivity.InfinityCategories.vertexFiberPullbackIso_hom_ι,
    ``SerrePositivity.InfinityCategories.vertexFiberTransport_ι,
    ``SerrePositivity.InfinityCategories.vertexFiber_kanComplex_of_leftFibration]
  for name in names do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "R: unexpected axioms in {name}: {axioms}"
  logInfo m!"R direct-reference audit passed: {names.size} declarations, standard three axioms only."

/-!
移動前の F1・Stable の一括監査は宣言元モジュールで対象を選ぶため、
Core へ移した全宣言（生成宣言を含む）はここで同じ三公理条件を検査する。
各移動先から少なくとも一つの宣言を実際に検査したことも確認する。
-/
open Lean in
run_cmd do
  let env ← getEnv
  let movedModules : Array Name := #[
    `SerrePositivity.InfinityCategories.Core.ConeDiagramReverse,
    `SerrePositivity.InfinityCategories.Core.JoinAssociator,
    `SerrePositivity.InfinityCategories.Core.JoinAssociatorBoundary,
    `SerrePositivity.InfinityCategories.Core.JoinAssociatorFactors,
    `SerrePositivity.InfinityCategories.Core.JoinAssociatorMiddle,
    `SerrePositivity.InfinityCategories.Core.JoinAugmented,
    `SerrePositivity.InfinityCategories.Core.JoinCutCalculus,
    `SerrePositivity.InfinityCategories.Core.JoinReassociation,
    `SerrePositivity.InfinityCategories.Core.JoinReassociationNaturality,
    `SerrePositivity.InfinityCategories.Core.JoinReverse,
    `SerrePositivity.InfinityCategories.Core.JoinReverseBoundary,
    `SerrePositivity.InfinityCategories.Core.JoinReverseCuts,
    `SerrePositivity.InfinityCategories.Core.JoinReverseEquiv,
    `SerrePositivity.InfinityCategories.Core.JoinReverseFactors,
    `SerrePositivity.InfinityCategories.Core.JoinReverseIntervals,
    `SerrePositivity.InfinityCategories.Core.JoinReverseNaturality,
    `SerrePositivity.InfinityCategories.Core.SliceOpposite,
    `SerrePositivity.InfinityCategories.Core.VertexFiberPullback,
    `SerrePositivity.InfinityCategories.Core.LeftFiberKan,
    `SerrePositivity.InfinityCategories.Core.PrismVerticalSimplex,
    `SerrePositivity.InfinityCategories.Core.NerveUnderMap,
    `SerrePositivity.InfinityCategories.Core.VertexFiberNervePullback]
  let mut checkedModules : Array Name := #[]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless movedModules.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "R moved Core module: unexpected axioms in {name}: {axioms}"
    unless checkedModules.contains mod do
      checkedModules := checkedModules.push mod
    count := count + 1
  for mod in movedModules do
    unless checkedModules.contains mod do
      throwError "R moved Core module was not audited: {mod}"
  logInfo m!"R moved-module origin audit passed: {count} declarations from {checkedModules.size} modules, standard three axioms only."
