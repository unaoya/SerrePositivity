import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.All
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Diagram,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.FilteredExactness,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationGraded,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Columns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ComplexColimit,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendSimplex,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationColumns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ZeroShift,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Edge,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ShiftPostcomposition,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationEdge,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ModuleColimit,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.EdgeObjects,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.EdgeCoefficients,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendColumn,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationTheta,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendClosed,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomExchange,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.FiniteBounds,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.NormalizedEndRebase,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Augmentation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.EndDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendMaurerCartan,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyDiagram,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFiniteSupport,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFiltration,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFiltrationDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentDegreeFiltration,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentDegreeDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyEdges,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DegreeSubcomplex,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentStages,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.FilteredModuleUnion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentStageColimit,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroStage,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstClosed,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarSimplicial,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarAugmentation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentVertexInclusion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarTopAppend,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarTopContraction,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarTopExact,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarIndexMap,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoproductIndexEmbedding,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarLowerIndex,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarLowerEmbedding,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarLowerCover,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarFilteredExact,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarDegreeOne,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarCokernelData,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarCokernel,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarZeroHomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentDimensionLayers,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerAnnihilation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerSurjectivity,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerRemainder,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerShortExact,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarSplittingIndex,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.WeightedCoproductDecomposition,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarSplittingCoefficients,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarSplitting,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ComplexCoproductHomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerHomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerCoefficients,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstHomologyComplex,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroStageIso,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstHomologyObjects,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerCycleBoundary,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerConnectingRepresentative,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarNondegFaces,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarNondegDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ComplexHomologyCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstLayerProjection,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ComplexCoproductHomologyLegs,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ComplexCoproductHomologyInclusions,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ModuleCoproductHomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerHomologyInclusions,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerCoefficientInclusions,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ShiftUnitValues,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ShiftUnitSigns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ShiftBlockValues,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.SignedShiftBlockValues,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstLayerHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DegreeOneHomologyMap,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DegreeOneHomologyRepresentative,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstLayerEvaluation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstLayerHomologyMap,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstLayerConnecting,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DegreeOneCyclesMap,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DegreeOneHomologyNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ComplexShiftHomologyCycles,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DegreeOneShiftHomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.SignedShiftBlockHomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DegreeOneHomologyLinear,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentNondegLayerColumns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstTail,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomTargetTransportPostcomposition,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.TransportedShiftBlockHomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFaceBlockHomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentPrefixBlockHomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentPrefixEdgeRaw,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentPrefixDiagramEdge,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentPrefixEdgeClosed,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentVertexHomologyTransport,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentPrefixHomologyDiagram,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFaceHomologyDiagram,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentNaturalLayerHomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyFaceIndices,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentPositiveFaceCoefficient,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyEqualities,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroFaceCoefficient,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstFaceSigns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentSignedLayerFaces,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentSignedLayerFaceColumns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerFaceHomologySum,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerFaceHomologyLegs,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstHomologyColumns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerFaceHomologyMatrix,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ModuleCoproductHomologyInclusions,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstHomologyDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ComplexCycleElements,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstHomologyComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ComplexHomologyClassBoundary,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerHomologyExact,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentStageHomologySupport,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentStageHomologyDescent,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroStageHomologySurjective,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroStageFiniteKernel,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentStageKernelDescent,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroStageKernel,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyCokernel,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyBarCofork,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyBarCokernel,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyColimit,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictHomologyDiagram,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.FilteredHomologyColimit,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.FilteredHomologyColimitLegs,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AugmentationComponents,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarNondegCokernel,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictHomologyColimit,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ZeroStageAugmentation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictHomologyCocone,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarNondegAugmentationLegs,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictZeroLayerCoefficients,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictAugmentationHomologyLegs,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictAugmentationHomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictAugmentationQuasiIso,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.KappaFilteredComparisonC1,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DerivedBarDiagram,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DerivedBarVertexComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DerivedBarComparisonReduction,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutGraded,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.MaurerCartanRestriction,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentBarProjective,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutColimit,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutDiagram,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutGradedSplit,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutGradedSplitting,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutLayerProjection,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutModule,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutProjective,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutTheta,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutTransition,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutZero,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentGradedProjective,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.MaurerCartanInclusionComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.MaurerCartanModuleMap,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.MaurerCartanZeroIso,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentBarQuasiIsoCriterion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCoconeHomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCoconeModuleMap,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyHomotopy,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyHomotopyComponent,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyHomotopyIso,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ProjectiveBarNativeCocone,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.SemifreeNativeColimit,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroLayerInclusion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ProjectiveBarVertexIso,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.QuasiIsoEdgeRecovery,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ResolvedCoherentHomology,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.SemifreeBarVertexCriterion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictNativeCocone,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictResolutionDiagramIso,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.TerminalHomologyCocone,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.TerminalHomologyExactness,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.UniversalMapColumns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ZeroLayerHomologyAugmentation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ZeroLayerNativeColumn]
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

#check SerrePositivity.InfinityCategories.dgCoherentBarStrictDiagram
#check SerrePositivity.InfinityCategories.dgCoherentBarStrictNormalizedModule
#check SerrePositivity.InfinityCategories.dgCoherentBarStrictAugmentationGraded
#check SerrePositivity.InfinityCategories.dgStrictFilteredColimit_quasiIso

#check SerrePositivity.InfinityCategories.dgStrictFilteredModuleColimit_quasiIso
#check SerrePositivity.InfinityCategories.dgCoherentBarStrictAugmentation_postNormalizedTheta
#check SerrePositivity.InfinityCategories.dgStrictAppendHom
#check SerrePositivity.InfinityCategories.dgStrictNormalizedDegree_finiteSupport

#check SerrePositivity.InfinityCategories.dgCoherentBarStrictColimitAugmentation
#check SerrePositivity.InfinityCategories.dgStrictNormalizedEndRebase_d

#check SerrePositivity.InfinityCategories.dgCoherentBarHomologyDiagram
#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizedDegree_boundedSupport
#check SerrePositivity.InfinityCategories.dgCoherentBarHigherPrefixColumn_mem_filtration
#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizedHomFiltration_theta

#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizedDegreeFiltration_d
#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizedStageComplex
#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizedStagesIsColimit
#check SerrePositivity.InfinityCategories.dgCoherentBarHomologyDiagramObjIso_naturality

#check SerrePositivity.InfinityCategories.dgCoherentBarFirstColumn_d
#check SerrePositivity.InfinityCategories.dgCoherentBarColumn_sub_first_mem_filtration
#check SerrePositivity.InfinityCategories.dgHomologyBarColimitAugmented
#check SerrePositivity.InfinityCategories.dgCoherentBarVertexHomologyMap

#check SerrePositivity.InfinityCategories.dgHomologyBarTopHomotopy_positive
#check SerrePositivity.InfinityCategories.dgHomologyBarLowerMap_covers
#check SerrePositivity.InfinityCategories.dgHomologyBarFiltered_exactAt

#check SerrePositivity.InfinityCategories.dgHomologyBarAugmentationIsCokernel
#check SerrePositivity.InfinityCategories.dgHomologyBarZeroHomologyColimitIso

#check SerrePositivity.InfinityCategories.dgCoherentBarStageToLayer
#check SerrePositivity.InfinityCategories.dgCoherentBarLayerSequence_shortExact

#check SerrePositivity.InfinityCategories.dgHomologyBarNondegZeroHomologyIso
#check SerrePositivity.InfinityCategories.dgHomologyBarNondeg_exactAt
#check SerrePositivity.InfinityCategories.dgComplexCoproductHomologyIso

#check SerrePositivity.InfinityCategories.dgCoherentBarLayerHomologyCoefficientsIso
#check SerrePositivity.InfinityCategories.dgCoherentBarFirstHomologyComplex
#check SerrePositivity.InfinityCategories.dgCoherentBarZeroStageIso
#check SerrePositivity.InfinityCategories.dgCoherentBarFirstHomologyObjectIso
#check SerrePositivity.InfinityCategories.dgCoherentBarLayerConnecting_representative

#check SerrePositivity.InfinityCategories.dgHomologyBarNondegDifferential
#check SerrePositivity.InfinityCategories.dgCoherentBarColumn_projected_first
#check SerrePositivity.InfinityCategories.dgComplexCoproductHomologyIso_ι
#check SerrePositivity.InfinityCategories.dgCoherentBarLayerHomologyIso_ι
#check SerrePositivity.InfinityCategories.dgCoherentBarLayerHomologyCoefficientsIso_ι

#check SerrePositivity.InfinityCategories.dgBarSignedShiftBlock_v
#check SerrePositivity.InfinityCategories.dgCoherentBarLayerFirstHom_d
#check SerrePositivity.InfinityCategories.dgCoherentBarLayerFirstHom_eval
#check SerrePositivity.InfinityCategories.dgCoherentBarLayerConnecting_eq_firstHomology

#check SerrePositivity.InfinityCategories.dgBarSignedShiftHomology
#check SerrePositivity.InfinityCategories.dgCoherentBarSignedFaceHomology
#check SerrePositivity.InfinityCategories.dgCoherentBarSignedPrefixHomology

#check SerrePositivity.InfinityCategories.dgCoherentBarPrefixCycle_eq_diagramEdge
#check SerrePositivity.InfinityCategories.dgCoherentBarSignedPrefixHomologyDiagram
#check SerrePositivity.InfinityCategories.dgCoherentBarSignedFaceHomologyDiagram

#check SerrePositivity.InfinityCategories.dgCoherentBarNaturalLayerHomologyIso_ι
#check SerrePositivity.InfinityCategories.dgCoherentBarSignedPositiveFaceCoefficient
#check SerrePositivity.InfinityCategories.dgCoherentBarSignedZeroFaceCoefficient

#check SerrePositivity.InfinityCategories.dgCoherentBarFirstHomologyComparison
#check SerrePositivity.InfinityCategories.dgCoherentBarFirstHomology_exactAt
#check SerrePositivity.InfinityCategories.dgCoherentBarFirstHomologyZeroIso
#check SerrePositivity.InfinityCategories.dgComplexHomologyClass_eq_zero_iff

#check SerrePositivity.InfinityCategories.dgCoherentBarZeroStageHomology_surjective
#check SerrePositivity.InfinityCategories.dgCoherentBarZeroStageHomology_kernel

#check SerrePositivity.InfinityCategories.dgCoherentBarHomologyIsCokernel

#check SerrePositivity.InfinityCategories.dgCoherentBarHomologyColimitIso

#check SerrePositivity.InfinityCategories.dgStrictCoherentHomologyColimitIso_leg
#check SerrePositivity.InfinityCategories.dgCoherentBarZeroStage_augmentation
#check SerrePositivity.InfinityCategories.dgHomologyBarNondegAugmentationIsCokernel

#check SerrePositivity.InfinityCategories.dgCoherentBarStrictColimitAugmentation_quasiIso
#check SerrePositivity.InfinityCategories.dgKappaCoherentBarHomologyColimitIso
#check SerrePositivity.InfinityCategories.dgKappaStrictBarColimitAugmentation_quasiIso

#check SerrePositivity.InfinityCategories.dgKappaStrictDerivedBarCocone_vertexIso
#check SerrePositivity.InfinityCategories.dgKappaStrictFilteredColimitComparison_of_barImageIsColimit

#check SerrePositivity.InfinityCategories.dgCoherentBarCutProjector_recover
#check SerrePositivity.InfinityCategories.dgBarModuleMaurerCartan_restrict

#check SerrePositivity.InfinityCategories.dgCoherentBarCutModule_projective
#check SerrePositivity.InfinityCategories.dgCoherentBarCutModuleIsColimit
#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizedModule_homotopicallyProjective

#check SerrePositivity.InfinityCategories.dgProjectiveBarNativeCocone_isColimit
#check SerrePositivity.InfinityCategories.dgSemifreeCoherent_hasColimit
#check SerrePositivity.InfinityCategories.dgCoherentBarMap_quasiIso
#check SerrePositivity.InfinityCategories.dgCoherentBarCoconeModuleMap
#check SerrePositivity.InfinityCategories.dgCoherentCoconeHomology
#check SerrePositivity.InfinityCategories.dgCoherentBarHomologyHomotopyIso

#check SerrePositivity.InfinityCategories.dgBarResolvedCoherentHomologyIso
#check SerrePositivity.InfinityCategories.dgBarResolvedColimitTerminalHomologyIsColimit
#check SerrePositivity.InfinityCategories.dgSemifreeCoherent_barVertexComparison
#check SerrePositivity.InfinityCategories.dgBarStrictResolutionDiagramIso
#check SerrePositivity.InfinityCategories.dgBarZeroLayerInclusion_homology
#check SerrePositivity.InfinityCategories.dgBarZeroLayerInclusion_nativeColumn
