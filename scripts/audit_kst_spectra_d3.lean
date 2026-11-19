import SerrePositivity.KST.Spectra.D3All
import Lean.Util.CollectAxioms

/-!
概要：Sp-2 専用集約の全 Spectra 宣言と推移的公理依存を監査する。
方針：私有宣言も元モジュールから列挙し、型の ModelCategory と非標準公理を拒否する。
規約：既存集約と既存監査は変更しない。未完の nativeLoop 同値を認証したとは扱わない。
使われ方：d3 の保存単位の独立監査。
-/

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  -- Preserve the original audit scope for these IC-2 modules.
  let ic2MovedFrom1 : Array Name := #[
    `SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.D3DoubleEndpointJointFamily,
    `SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.D3JointSourceStageComparison]
  let env ← getEnv
  for mod in env.header.modules do
    if (`SerrePositivity.KST.Fibration).isPrefixOf mod.module ||
        (`SerrePositivity.KST.LocalizingInvariants).isPrefixOf mod.module then
      throwError "Sp-2 d3: downstream K dependency imported: {mod.module}"
  for mod in #[
      `SerrePositivity.KST.Spectra.PointedParametricUncurryAction,
      `SerrePositivity.KST.Spectra.PointedParametricUncurryPre,
      `SerrePositivity.KST.Spectra.PointedUncurryActionTensor,
      `SerrePositivity.KST.Spectra.PointedUncurryComposition] do
    if env.header.modules.any (·.module == mod) then
      throwError "Sp-2 d3: disconnected leaf imported: {mod}"
  let expected := #[
    `SerrePositivity.KST.Spectra.SpectrumFiniteLimits,
    `SerrePositivity.KST.Spectra.AdjointLoopRelativeFullCoherentComparison,
    `SerrePositivity.KST.Spectra.AdjointLoopRelativeDiagramResolution,
    `SerrePositivity.KST.Spectra.D3ComparisonResolution,
    `SerrePositivity.KST.Spectra.D3NativeLoopSource,
    `SerrePositivity.KST.Spectra.D3RawHomVertices,
    `SerrePositivity.KST.Spectra.D3LoopUnitExtension,
    `SerrePositivity.KST.Spectra.D3LoopSourceComparison,
    `SerrePositivity.KST.Spectra.D3LoopSourceCone,
    `SerrePositivity.KST.Spectra.D3LoopConeRelativeLifting,
    `SerrePositivity.KST.Spectra.D3ComparisonHomLifting,
    `SerrePositivity.KST.Spectra.D3CompositeCorner,
    `SerrePositivity.KST.Spectra.D3SpectrumCorner,
    `SerrePositivity.KST.Spectra.D3CommonRefinement,
    `SerrePositivity.KST.Spectra.D3CommonHom,
    `SerrePositivity.KST.Spectra.D3CommonHomComposition,
    `SerrePositivity.KST.Spectra.D3CommonHomLaws,
    `SerrePositivity.KST.Spectra.D3CommonEnrichment,
    `SerrePositivity.KST.Spectra.D3CommonCoherentComparison,
    `SerrePositivity.KST.Spectra.D3CommonProjectionNaturality,
    `SerrePositivity.KST.Spectra.D3ConeForwardTransport,
    `SerrePositivity.KST.Spectra.D3CommonLoopCone,
    `SerrePositivity.KST.Spectra.D3CommonLoopSquare,
    `SerrePositivity.KST.Spectra.D3CommonLoopInterval,
    `SerrePositivity.KST.Spectra.D3CommonLoopDiagramResolution,
    `SerrePositivity.KST.Spectra.D3CommonLoopDiagramSection,
    `SerrePositivity.KST.Spectra.D3StageEvaluation,
    `SerrePositivity.KST.Spectra.D3CommonStageProjection,
    `SerrePositivity.KST.Spectra.D3CommonStageLoop,
    `SerrePositivity.KST.Spectra.D3StagePullback,
    `SerrePositivity.KST.Spectra.D3StageLoopCone,
    `SerrePositivity.KST.Spectra.D3StageLoopSquare,
    `SerrePositivity.KST.Spectra.D3StageLoopDiagramFamily,
    `SerrePositivity.KST.Spectra.D3PointedKanIhom,
    `SerrePositivity.KST.Spectra.D3EnrichedOrderedDiagram,
    `SerrePositivity.KST.Spectra.D3PointedKanParameterDiagram,
    `SerrePositivity.KST.Spectra.D3PointedKanParameterSquare,
    `SerrePositivity.KST.Spectra.D3EndpointParameterSquare,
    `SerrePositivity.KST.Spectra.D3PointedKanParameterVertex,
    `SerrePositivity.KST.Spectra.D3PointedKanEndpointZeros,
    `SerrePositivity.KST.Spectra.D3PointedKanCofiberCone,
    `SerrePositivity.KST.Spectra.D3StrictPullbackSquare,
    `SerrePositivity.KST.Spectra.D3PointedKanEndpointLoopDiagram,
    `SerrePositivity.KST.Spectra.D3PointedKanUnitIso,
    `SerrePositivity.KST.Spectra.D3LoopDiagramTransport,
    `SerrePositivity.KST.Spectra.D3PointedKanLoopSection,
    `SerrePositivity.KST.Spectra.D3CommonStageSourceComparison,
    `SerrePositivity.KST.Spectra.D3StageStructure,
    `SerrePositivity.KST.Spectra.D3CommonStageStructure,
    `SerrePositivity.KST.Spectra.D3StageStructureFunctor,
    `SerrePositivity.KST.Spectra.D3StageLoopStructureFamily,
    `SerrePositivity.KST.Spectra.D3StageDiagramProjection,
    `SerrePositivity.KST.Spectra.D3FunctorIsoEvaluation,
    `SerrePositivity.KST.Spectra.D3StageDiagramCorners,
    `SerrePositivity.KST.Spectra.D3LoopCanonicalNaturality,
    `SerrePositivity.KST.Spectra.D3CommonStageCanonicalCoherence,
    `SerrePositivity.KST.Spectra.D3StageLoopedCanonical,
    `SerrePositivity.KST.Spectra.D3StageLoopedCanonicalProjection,
    `SerrePositivity.KST.Spectra.D3StageLoopImageComparison,
    `SerrePositivity.KST.Spectra.D3GradedTransformationAlgebra,
    `SerrePositivity.KST.Spectra.D3GradedCompositionNerve,
    `SerrePositivity.KST.Spectra.D3ProjectionStructureGraded,
    `SerrePositivity.KST.Spectra.D3GradedWhiskeringNerve,
    `SerrePositivity.KST.Spectra.D3GradedWhiskeringHom,
    `SerrePositivity.KST.Spectra.D3ProjectionStructureIso,
    `SerrePositivity.KST.Spectra.D3LoopCanonicalSectionTransport,
    `SerrePositivity.KST.Spectra.D3StageStructureTail,
    `SerrePositivity.KST.Spectra.D3CommonStageTargetStructure,
    `SerrePositivity.KST.Spectra.D3CommonStageRefinedPasting,
    `SerrePositivity.KST.Spectra.D3StageLoopedUnitTriangle,
    `SerrePositivity.KST.Spectra.D3StageStructureCoherenceCriterion,
    `SerrePositivity.KST.Spectra.D3StageCoherencePastingCounterexample,
    `SerrePositivity.KST.Spectra.D3StageStructureDefect,
    `SerrePositivity.KST.Spectra.D3LoopDiagramTranspose,
    `SerrePositivity.KST.Spectra.D3LoopDiagramReflection,
    `SerrePositivity.KST.Spectra.D3NativeLoopReflection,
    `SerrePositivity.KST.Spectra.D3LoopReflectionImage,
    `SerrePositivity.KST.Spectra.D3ComparisonOutput,
    `SerrePositivity.KST.Spectra.D3ReflectionSourceImage,
    `SerrePositivity.KST.Spectra.D3StageReflectionStructure,
    `SerrePositivity.KST.Spectra.D3StageLoopReflectedComparison,
    `SerrePositivity.KST.Spectra.D3StageReflectedStructureCriterion,
    `SerrePositivity.KST.Spectra.D3StageAlternatingComparison,
    `SerrePositivity.KST.Spectra.D3TensorParameterDiagram,
    `SerrePositivity.KST.Spectra.D3BiParameterSquare,
    `SerrePositivity.KST.Spectra.D3BiParameterFaces,
    `SerrePositivity.KST.Spectra.D3DoubleEndpointCorners,
    `SerrePositivity.KST.Spectra.D3ParameterPullbackCriterion,
    `SerrePositivity.KST.Spectra.D3DoubleEndpointPullbacks,
    `SerrePositivity.KST.Spectra.D3TensorEndpointZeros,
    `SerrePositivity.KST.Spectra.D3DoubleEndpointLoopFamilies,
    `SerrePositivity.KST.Spectra.D3DoubleEndpointModelComparison,
    `SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.D3DoubleEndpointJointFamily,
    `SerrePositivity.KST.Spectra.D3ParameterDiagramTransformation,
    `SerrePositivity.KST.Spectra.D3ParameterUnitComparison,
    `SerrePositivity.KST.Spectra.D3ParameterComparisonStage,
    `SerrePositivity.KST.Spectra.D3PointedKanPreIsoAlgebra,
    `SerrePositivity.KST.Spectra.D3JointUnitStageComparison,
    `SerrePositivity.KST.Spectra.D3JointModelStageComparison,
    `SerrePositivity.KST.Spectra.D3DoubleEndpointLoopImageComparison,
    `SerrePositivity.KST.Spectra.D3LoopedSectionComparison,
    `SerrePositivity.KST.Spectra.D3CurryEvaluationProjection,
    `SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.D3JointSourceStageComparison,
    `SerrePositivity.KST.Spectra.D3LoopImageComparisonCorners,
    `SerrePositivity.KST.Spectra.D3LoopedSectionComparisonCorners,
    `SerrePositivity.KST.Spectra.D3LoopedSectionUnitPasting,
    `SerrePositivity.KST.Spectra.D3DoubleEndpointUnitPasting,
    `SerrePositivity.KST.Spectra.D3CanonicalImageDoubleEndpointComparison,
    `SerrePositivity.KST.Spectra.D3ParameterSquareComparison,
    `SerrePositivity.KST.Spectra.D3DoubleEndpointUnitDiagramComparison,
    `SerrePositivity.KST.Spectra.D3EquivalencePathIsoValues,
    `SerrePositivity.KST.Spectra.D3FiberPathIsoComparison,
    `SerrePositivity.KST.Spectra.D3PathCorrectedComponentValue,
    `SerrePositivity.KST.Spectra.D3PointedKanSectionTargetValue,
    `SerrePositivity.KST.Spectra.D3SectionUnitFaceComparison,
    `SerrePositivity.KST.Spectra.D3UnitLoopSourceNaturality,
    `SerrePositivity.KST.Spectra.D3DoubleEndpointTargetAgreement,
    `SerrePositivity.KST.Spectra.D3RetainedDoubleEndpointComparison,
    `SerrePositivity.KST.Spectra.D3CanonicalImageUnitPasting,
    `SerrePositivity.KST.Spectra.D3DoubleEndpointSourcePasting,
    `SerrePositivity.KST.Spectra.D3UniversalLoopModelCorrection,
    `SerrePositivity.KST.Spectra.D3UniversalLoopModelStages,
    `SerrePositivity.KST.Spectra.D3IteratedLoopDiagramReflection,
    `SerrePositivity.KST.Spectra.D3DoubleEndpointIteratedLoops,
    `SerrePositivity.KST.Spectra.D3IteratedLoopDiagramProjection,
    `SerrePositivity.KST.Spectra.D3DoubleEndpointOrderComparison,
    `SerrePositivity.KST.Spectra.D3DoubleEndpointOrderFaces,
    `SerrePositivity.KST.Spectra.D3DoubleEndpointOrderModels,
    `SerrePositivity.KST.Spectra.D3DoubleEndpointOrderCorrection,
    `SerrePositivity.KST.Spectra.D3BoundaryComparisonResolution,
    `SerrePositivity.KST.Spectra.D3BoundaryComparisonLifting]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless ((`SerrePositivity.KST.Spectra).isPrefixOf mod || ic2MovedFrom1.contains mod) do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "Sp-2 d3: ModelCategory assumption in type of {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Sp-2 d3: unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if count == 0 then throwError "Sp-2 d3: no declarations audited"
  for mod in expected do
    unless modules.contains mod do throwError "Sp-2 d3: required module missing: {mod}"
  logInfo m!"Sp-2 d3: {count} declarations in {modules.size} modules audited; standard three axioms only."
