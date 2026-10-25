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
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentPrefixBlockHomology]
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
