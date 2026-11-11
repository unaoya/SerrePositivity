import SerrePositivity.InfinityCategories.Project.Entrypoints.DerivedCoherentBarStrictComparisonAll
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.Diagram,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.FilteredExactness,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AugmentationGraded,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.Columns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexColimit,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AppendSimplex,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AugmentationColumns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ZeroShift,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.Edge,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ShiftPostcomposition,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AugmentationEdge,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ModuleColimit,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.EdgeObjects,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.EdgeCoefficients,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AppendColumn,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AugmentationTheta,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AppendClosed,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomExchange,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AppendHom,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.FiniteBounds,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AppendDifferential,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.NormalizedEndRebase,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.Augmentation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.EndDifferential,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AppendMaurerCartan,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyDiagram,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFiniteSupport,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFiltration,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFiltrationDifferential,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentDegreeFiltration,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentDegreeDifferential,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyEdges,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DegreeSubcomplex,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentStages,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.FilteredModuleUnion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentStageColimit,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstDifferential,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentZeroStage,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstClosed,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarSimplicial,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarAugmentation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentVertexInclusion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarTopAppend,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarTopContraction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarTopExact,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarIndexMap,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoproductIndexEmbedding,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarLowerIndex,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarLowerEmbedding,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarLowerCover,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarFilteredExact,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarDegreeOne,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarCokernelData,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarCokernel,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarZeroHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentDimensionLayers,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerAnnihilation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerDifferential,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerSurjectivity,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerRemainder,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerShortExact,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarSplittingIndex,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.WeightedCoproductDecomposition,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarSplittingCoefficients,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarSplitting,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexCoproductHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerCoefficients,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstHomologyComplex,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentZeroStageIso,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstHomologyObjects,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerCycleBoundary,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerConnectingRepresentative,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarNondegFaces,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarNondegDifferential,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexHomologyCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstLayerProjection,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexCoproductHomologyLegs,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexCoproductHomologyInclusions,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ModuleCoproductHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerHomologyInclusions,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerCoefficientInclusions,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ShiftUnitValues,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ShiftUnitSigns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ShiftBlockValues,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.SignedShiftBlockValues,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstLayerHom,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DegreeOneHomologyMap,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DegreeOneHomologyRepresentative,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstLayerEvaluation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstLayerHomologyMap,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstLayerConnecting,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DegreeOneCyclesMap,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DegreeOneHomologyNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexShiftHomologyCycles,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DegreeOneShiftHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.SignedShiftBlockHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DegreeOneHomologyLinear,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentNondegLayerColumns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstTail,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomTargetTransportPostcomposition,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.TransportedShiftBlockHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFaceBlockHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentPrefixBlockHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentPrefixEdgeRaw,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentPrefixDiagramEdge,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentPrefixEdgeClosed,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentVertexHomologyTransport,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentPrefixHomologyDiagram,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFaceHomologyDiagram,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentNaturalLayerHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyFaceIndices,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentPositiveFaceCoefficient,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyEqualities,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentZeroFaceCoefficient,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstFaceSigns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentSignedLayerFaces,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentSignedLayerFaceColumns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerFaceHomologySum,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerFaceHomologyLegs,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstHomologyColumns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerFaceHomologyMatrix,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ModuleCoproductHomologyInclusions,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstHomologyDifferential,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexCycleElements,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstHomologyComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexHomologyClassBoundary,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerHomologyExact,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentStageHomologySupport,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentStageHomologyDescent,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentZeroStageHomologySurjective,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentZeroStageFiniteKernel,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentStageKernelDescent,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentZeroStageKernel,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyCokernel,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyBarCofork,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyBarCokernel,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyColimit,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictHomologyDiagram,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.FilteredHomologyColimit,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.FilteredHomologyColimitLegs,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AugmentationComponents,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarNondegCokernel,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictHomologyColimit,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ZeroStageAugmentation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictHomologyCocone,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarNondegAugmentationLegs,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictZeroLayerCoefficients,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictAugmentationHomologyLegs,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictAugmentationHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictAugmentationQuasiIso,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.KappaFilteredComparisonC1,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DerivedBarDiagram,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DerivedBarVertexComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DerivedBarComparisonReduction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutGraded,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.MaurerCartanRestriction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentBarProjective,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutColimit,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutDiagram,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutGradedSplit,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutGradedSplitting,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutLayerProjection,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutModule,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutProjective,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutTheta,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutTransition,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCutZero,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentGradedProjective,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.MaurerCartanInclusionComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.MaurerCartanModuleMap,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.MaurerCartanZeroIso,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentBarQuasiIsoCriterion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCoconeHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCoconeModuleMap,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyHomotopy,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyHomotopyComponent,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyHomotopyIso,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ProjectiveBarNativeCocone,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.SemifreeNativeColimit,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentZeroLayerInclusion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ProjectiveBarVertexIso,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.QuasiIsoEdgeRecovery,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ResolvedCoherentHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.SemifreeBarVertexCriterion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictNativeCocone,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictResolutionDiagramIso,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.TerminalHomologyCocone,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.TerminalHomologyExactness,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.UniversalMapColumns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ZeroLayerHomologyAugmentation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ZeroLayerNativeColumn,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ClosedEdgeRecovery,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ClosedHomTransport,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoconeHomologyLegs,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoconeVertexRecovery,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentVertexHomologyTransportGeneral,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DerivedCoherentAugmentation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DerivedStrictFilteredComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ExtendedCoconeHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ExtendedCoconeVertexMaps,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ExtendedHomologyRestriction,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ExtendedNativeCocone,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.NativeVertexModuleMaps,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.SemifreeHomologyColimitCriterion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.TerminalNativeLeg,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.UniversalCoconeHomology,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ZeroShiftIn,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.UnconditionalCovers]
  let mut count := 0
  let mut seen : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    if info.isAxiom then throwError "New axiom: {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    if (info.type.find? fun e => match e with
      | .const n _ => n.getString! == "ModelCategory"
      | _ => false).isSome then
      throwError "ModelCategory assumption in {name}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"D-e strict bar audit passed: {count} declarations in {seen.size} modules."

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictNormalizedModule
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentationGraded
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictFilteredColimit_quasiIso

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictFilteredModuleColimit_quasiIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentation_postNormalizedTheta
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendHom
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictNormalizedDegree_finiteSupport

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictColimitAugmentation
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictNormalizedEndRebase_d

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegree_boundedSupport
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHigherPrefixColumn_mem_filtration
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedHomFiltration_theta

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration_d
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStagesIsColimit
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso_naturality

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstColumn_d
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarColumn_sub_first_mem_filtration
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarColimitAugmented
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarVertexHomologyMap

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarTopHomotopy_positive
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerMap_covers
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFiltered_exactAt

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarAugmentationIsCokernel
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarZeroHomologyColimitIso

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegZeroHomologyIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondeg_exactAt
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductHomologyIso

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerHomologyCoefficientsIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstHomologyComplex
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroStageIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstHomologyObjectIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerConnecting_representative

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegDifferential
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarColumn_projected_first
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCoproductHomologyIso_ι
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerHomologyIso_ι
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerHomologyCoefficientsIso_ι

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarSignedShiftBlock_v
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFirstHom_d
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFirstHom_eval
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerConnecting_eq_firstHomology

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarSignedShiftHomology
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedFaceHomology
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedPrefixHomology

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarPrefixCycle_eq_diagramEdge
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedPrefixHomologyDiagram
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedFaceHomologyDiagram

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNaturalLayerHomologyIso_ι
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedPositiveFaceCoefficient
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedZeroFaceCoefficient

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstHomologyComparison
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstHomology_exactAt
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstHomologyZeroIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass_eq_zero_iff

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroStageHomology_surjective
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroStageHomology_kernel

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyIsCokernel

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyColimitIso

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictCoherentHomologyColimitIso_leg
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroStage_augmentation
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegAugmentationIsCokernel

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictColimitAugmentation_quasiIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgKappaCoherentBarHomologyColimitIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgKappaStrictBarColimitAugmentation_quasiIso

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgKappaStrictDerivedBarCocone_vertexIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgKappaStrictFilteredColimitComparison_of_barImageIsColimit

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjector_recover
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarModuleMaurerCartan_restrict

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModule_projective
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModuleIsColimit
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedModule_homotopicallyProjective

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarNativeCocone_isColimit
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgSemifreeCoherent_hasColimit
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarMap_quasiIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCoconeModuleMap
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentCoconeHomology
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyHomotopyIso

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarResolvedCoherentHomologyIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarResolvedColimitTerminalHomologyIsColimit
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgSemifreeCoherent_barVertexComparison
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarStrictResolutionDiagramIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarZeroLayerInclusion_homology
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarZeroLayerInclusion_nativeColumn

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgKappaStrictFilteredColimitComparison_unconditional
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCone_covers_unconditional
