import SerrePositivity.KST.SConstruction.Cofinality
import Lean.Util.CollectAxioms

open CategoryTheory

/-!
概要：K-cof 所有葉の全宣言と推移的公理依存を監査する。
方針：実 import 元で所有宣言を列挙し、標準三公理だけであることを強制する。
規約：ModelCategory 型仮定と、採用済み狭い旗供給以外の K-B 依存を拒否する。
使われ方：K-cof の集約ビルド後の限定監査。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let owner := `SerrePositivity.KST.SConstruction.Cofinality
  let expected := #[
    `SerrePositivity.KST.SConstruction.Cofinality.CompleteSource,
    `SerrePositivity.KST.SConstruction.Cofinality.FullyFaithful,
    `SerrePositivity.KST.SConstruction.Cofinality.ZeroComparison,
    `SerrePositivity.KST.SConstruction.Cofinality.DiagramImage,
    `SerrePositivity.KST.SConstruction.Cofinality.MultiDiagramImage,
    `SerrePositivity.KST.SConstruction.Cofinality.StabilizedDiagramImage,
    `SerrePositivity.KST.SConstruction.Cofinality.StageDetection,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeDiagramImage,
    `SerrePositivity.KST.SConstruction.Cofinality.CompletionStabilization,
    `SerrePositivity.KST.SConstruction.Cofinality.MultiCompletion,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeFlags,
    `SerrePositivity.KST.SConstruction.Cofinality.WideStageInput,
    `SerrePositivity.KST.SConstruction.Cofinality.WideStageMaps,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagDiagram,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagZero,
    `SerrePositivity.KST.SConstruction.Cofinality.MultiRelativeFlags,
    `SerrePositivity.KST.SConstruction.Cofinality.SourceRelativeFlags,
    `SerrePositivity.KST.SConstruction.Cofinality.WideCompletionSupply,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeCoreEvaluation,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagDiagonalEvaluation,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagImageComponents,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagSourceRecovery,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagVertexRecovery,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeImageFlagEquivalence,
    `SerrePositivity.KST.SConstruction.Cofinality.WideInternalFlags,
    `SerrePositivity.KST.SConstruction.Cofinality.WideInvertibleReflection,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeCoreFlagIso,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagDiscreteness,
    `SerrePositivity.KST.SConstruction.Cofinality.ImageComponentObstruction,
    `SerrePositivity.KST.SConstruction.Cofinality.ImageComponentBasepoint,
    `SerrePositivity.KST.SConstruction.Cofinality.CompletionImageClosed,
    `SerrePositivity.KST.SConstruction.Cofinality.CompletionImageEquivalence,
    `SerrePositivity.KST.SConstruction.Cofinality.CompletionImageSComparison,
    `SerrePositivity.KST.SConstruction.Cofinality.CompletionImageDiagram,
    `SerrePositivity.KST.SConstruction.Cofinality.ImageInclusionKComparison,
    `SerrePositivity.KST.SConstruction.Cofinality.WideKZeroObstruction,
    `SerrePositivity.KST.SConstruction.Cofinality.KZeroObjectRepresentatives,
    `SerrePositivity.KST.SConstruction.Cofinality.WideHomotopyObjectClasses,
    `SerrePositivity.KST.SConstruction.Cofinality.WideBiproductEdges,
    `SerrePositivity.KST.SConstruction.Cofinality.WideComponentAddition,
    `SerrePositivity.KST.SConstruction.Cofinality.WideComponentGroup,
    `SerrePositivity.KST.SConstruction.Cofinality.WideTriangleAdditivity,
    `SerrePositivity.KST.SConstruction.Cofinality.KZeroToWideGroup,
    `SerrePositivity.KST.SConstruction.Cofinality.WideKZeroObstructionEquiv,
    `SerrePositivity.KST.SConstruction.Cofinality.CokernelStructureMaps,
    `SerrePositivity.KST.SConstruction.Cofinality.CanonicalWideNaturality,
    `SerrePositivity.KST.SConstruction.Cofinality.CokernelDiagram,
    `SerrePositivity.KST.SConstruction.Cofinality.ObstructionDiagramIso,
    `SerrePositivity.KST.SConstruction.Cofinality.CutKZeroAdditivity,
    `SerrePositivity.KST.SConstruction.Cofinality.CutKZeroRestriction,
    `SerrePositivity.KST.SConstruction.Cofinality.CutKZeroConstant,
    `SerrePositivity.KST.SConstruction.Cofinality.CutKZeroEquiv,
    `SerrePositivity.KST.SConstruction.Cofinality.CutCokernelRestriction,
    `SerrePositivity.KST.SConstruction.Cofinality.CutCokernelEquiv,
    `SerrePositivity.KST.SConstruction.Cofinality.GroupNerveHigherInput,
    `SerrePositivity.KST.SConstruction.Cofinality.CutCokernelLaws,
    `SerrePositivity.KST.SConstruction.Cofinality.CokernelEdgeCoordinates,
    `SerrePositivity.KST.SConstruction.Cofinality.CokernelTriangleCoordinates,
    `SerrePositivity.KST.SConstruction.Cofinality.CokernelIntervals,
    `SerrePositivity.KST.SConstruction.Cofinality.CokernelNerveSimplex,
    `SerrePositivity.KST.SConstruction.Cofinality.CokernelSimplicialSet,
    `SerrePositivity.KST.SConstruction.Cofinality.CokernelNerveMap,
    `SerrePositivity.KST.SConstruction.Cofinality.CokernelNerveCoordinates,
    `SerrePositivity.KST.SConstruction.Cofinality.CokernelBarIso,
    `SerrePositivity.KST.SConstruction.Cofinality.MultiCokernelRow,
    `SerrePositivity.KST.SConstruction.Cofinality.WideComponentBar,
    `SerrePositivity.KST.SConstruction.Cofinality.CanonicalComponentProjection,
    `SerrePositivity.KST.SConstruction.Cofinality.WideHeadDiscretization,
    `SerrePositivity.KST.SConstruction.Cofinality.WideHeadVanishing,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeEvaluationNaturality,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeHeadComparison,
    `SerrePositivity.KST.SConstruction.Cofinality.ClosedFlagSupplyComparison,
    `SerrePositivity.KST.SConstruction.Cofinality.ClosedFlagSupplyIso,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagStableModel,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagInclusionExact,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagSTranspose,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeSEdgeDetection,
    `SerrePositivity.KST.SConstruction.Cofinality.CoreFlagSupply,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeSSimplexDetection,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagSEvaluations,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeSTransposeWide,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeSTransposeLift,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeSEvaluationFlags,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeSInverseDiagram,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeSInverse,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeSInterchange,
    `SerrePositivity.KST.SConstruction.Cofinality.ClosedSFlagComparison,
    `SerrePositivity.KST.SConstruction.Cofinality.ClosedSFlagInclusion,
    `SerrePositivity.KST.SConstruction.Cofinality.ClosedSFlagNaturality,
    `SerrePositivity.KST.SConstruction.Cofinality.ClosedSFlagSNaturality,
    `SerrePositivity.KST.SConstruction.Cofinality.ClosedSFlagDiagramIso,
    `SerrePositivity.KST.SConstruction.Cofinality.ClosedRelativeRealizationIso,
    `SerrePositivity.KST.SConstruction.Cofinality.ClosedRelativeVanishing,
    `SerrePositivity.KST.SConstruction.Cofinality.ClosedRelativeExInfinityVanishing,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeFiberKanSquare,
    `SerrePositivity.KST.SConstruction.Cofinality.ClosedKernelExInfinityVanishing,
    `SerrePositivity.KST.SConstruction.Cofinality.KanPullbackCofinalityInput,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeKanFactor,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeKanProjection,
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeKanInclusion,
    `SerrePositivity.KST.SConstruction.Cofinality.SingleRealizationBoundary,
    `SerrePositivity.KST.SConstruction.Cofinality.CoreSPointedBoundary,
    `SerrePositivity.KST.SConstruction.Cofinality.BoundaryExInfinityTransfer,
    `SerrePositivity.KST.SConstruction.Cofinality.BoundaryKanTransfer,
    `SerrePositivity.KST.SConstruction.Cofinality.BoundaryKTransfer,
    `SerrePositivity.KST.SConstruction.Cofinality.CofinalityFromInputs,
    `SerrePositivity.KST.SConstruction.Cofinality.KanPullbackSupply,
    `SerrePositivity.KST.SConstruction.Cofinality.Thomason]
  -- 採用済み無条件 K-B2-S1 と相対四角形の正確な閉包。
  let approvedRelativeClosure := #[
    `SerrePositivity.KST.Fibration.ClosedCofiberRawProjection,
    `SerrePositivity.KST.Fibration.ClosedFlagCofiberCoordinates,
    `SerrePositivity.KST.Fibration.ClosedFlagCofiberPostcomparison,
    `SerrePositivity.KST.Fibration.ClosedFlagFiniteAllLengths,
    `SerrePositivity.KST.Fibration.ClosedFlagFiniteComparison,
    `SerrePositivity.KST.Fibration.ClosedFlagFiniteEquivalence,
    `SerrePositivity.KST.Fibration.ClosedFlagFiniteRecursion,
    `SerrePositivity.KST.Fibration.ClosedFlagOneComparison,
    `SerrePositivity.KST.Fibration.ClosedFlagOneEquivalence,
    `SerrePositivity.KST.Fibration.ClosedFlagPostCartesian,
    `SerrePositivity.KST.Fibration.ClosedKernelCoefficient,
    `SerrePositivity.KST.Fibration.ClosedKernelFiniteCoordinates,
    `SerrePositivity.KST.Fibration.ClosedKernelInitialPullback,
    `SerrePositivity.KST.Fibration.ClosedTailCanonicalComponents,
    `SerrePositivity.KST.Fibration.ClosedTailMultiStep,
    `SerrePositivity.KST.Fibration.CoreSinglePullbackTransfer,
    `SerrePositivity.KST.Fibration.FibrantPullbackCancellation,
    `SerrePositivity.KST.Fibration.KernelPostcomposition,
    `SerrePositivity.KST.Fibration.KilledKernelIso,
    `SerrePositivity.KST.Fibration.LocalizedFiniteProductEquality,
    `SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LocalizedPairBothEquality,
    `SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LocalizedPairEquality,
    `SerrePositivity.KST.Fibration.ProductCoefficientHomotopyPullback,
    `SerrePositivity.KST.Fibration.ProductCoordinatePullbackTransfer,
    `SerrePositivity.KST.Fibration.PullbackCancellation,
    `SerrePositivity.KST.Fibration.Relative.ClosedCofiberProjection,
    `SerrePositivity.KST.Fibration.Relative.ClosedFlagFactor,
    `SerrePositivity.KST.Fibration.Relative.ClosedStableFiber,
    `SerrePositivity.KST.Fibration.Relative.ClosedStableFiberUnconditional,
    `SerrePositivity.KST.Fibration.Relative.ClosedTailAdditivity,
    `SerrePositivity.KST.Fibration.Relative.ClosedTailFlags,
    `SerrePositivity.KST.Fibration.Relative.ClosedTailPullback,
    `SerrePositivity.KST.Fibration.Relative.ClosedZeroFlag,
    `SerrePositivity.KST.Fibration.Relative.StableTrivialPullback,
    `SerrePositivity.KST.Fibration.SimplicialInitialPullback,
    `SerrePositivity.KST.Fibration.StableTrivialPullbackSection,
    `SerrePositivity.KST.Fibration.VerdierKernelEquivalence,
    `SerrePositivity.KST.Fibration.WeakCofiberPostcomposition,
    `SerrePositivity.KST.Fibration.WeakCofiberRawProjection,
    `SerrePositivity.KST.Fibration.WeakStringFinitePostMap,

    `SerrePositivity.KST.Fibration.SpectrumZeroFromPositiveLevels,
    `SerrePositivity.KST.Fibration.ClosedTopIso,
    `SerrePositivity.KST.Fibration.CofiberFamilyTranspose,
    `SerrePositivity.KST.Fibration.CofiberFamilyUntranspose,
    `SerrePositivity.KST.Fibration.ComposableWeakArrowEndpointPullback,
    `SerrePositivity.KST.Fibration.ComposableWeakArrowObjectPullback,
    `SerrePositivity.KST.Fibration.ComposableWeakArrowPullback,
    `SerrePositivity.KST.Fibration.ComposableWeakArrowReflection,
    `SerrePositivity.KST.Fibration.ComposableWeakArrowSPullback,
    `SerrePositivity.KST.Fibration.ComposableWeakArrows,
    `SerrePositivity.KST.Fibration.CoreFactorPushout,
    `SerrePositivity.KST.Fibration.CoreFactorization,
    `SerrePositivity.KST.Fibration.FamilyExactness,
    `SerrePositivity.KST.Fibration.FinEmptyProductIso,
    `SerrePositivity.KST.Fibration.FinSnocProductIso,
    `SerrePositivity.KST.Fibration.FiniteFlagComparisonInduction,
    `SerrePositivity.KST.Fibration.FullFunctorCore,
    `SerrePositivity.KST.Fibration.FullPredicatePullback,
    `SerrePositivity.KST.Fibration.FullPredicateRestriction,
    `SerrePositivity.KST.Fibration.FullSubcomplexJointReflection,
    `SerrePositivity.KST.Fibration.FunctorCoreCriterion,
    `SerrePositivity.KST.Fibration.GappedPullback,
    `SerrePositivity.KST.Fibration.HornDiagramReflection,
    `SerrePositivity.KST.Fibration.InitialHornPoint,
    `SerrePositivity.KST.Fibration.InnerAnodyneCoreReflection,
    `SerrePositivity.KST.Fibration.JointReflection,
    `SerrePositivity.KST.Fibration.KernelCofiberModel,
    `SerrePositivity.KST.Fibration.ObjectSinglePairComparison,
    `SerrePositivity.KST.Fibration.ProductQuillenABaseChange,
    `SerrePositivity.KST.Fibration.ReindexJointReflection,
    `SerrePositivity.KST.Fibration.Relative.ClosedFlagConstants,
    `SerrePositivity.KST.Fibration.Relative.ClosedFlagFunctor,
    `SerrePositivity.KST.Fibration.Relative.ClosedKernelContraction,
    `SerrePositivity.KST.Fibration.Relative.ClosedKernelFlags,
    `SerrePositivity.KST.Fibration.Relative.ClosedRealizationPullback,
    `SerrePositivity.KST.Fibration.Relative.ClosedStableFlags,
    `SerrePositivity.KST.Fibration.RelativeCofiberBaseChange,
    `SerrePositivity.KST.Fibration.RelativeDiagram,
    `SerrePositivity.KST.Fibration.RelativeDiagramCore,
    `SerrePositivity.KST.Fibration.RelativeDiagramKernel,
    `SerrePositivity.KST.Fibration.RelativeDiagramMap,
    `SerrePositivity.KST.Fibration.RelativeGappedWeakString,
    `SerrePositivity.KST.Fibration.RelativePullback,
    `SerrePositivity.KST.Fibration.RelativePullbackIteration,
    `SerrePositivity.KST.Fibration.RelativePullbackMulti,
    `SerrePositivity.KST.Fibration.RelativePullbackRowPair,
    `SerrePositivity.KST.Fibration.RelativePullbackS,
    `SerrePositivity.KST.Fibration.RelativeSConstruction,
    `SerrePositivity.KST.Fibration.RelativeSFunctor,
    `SerrePositivity.KST.Fibration.RelativeSQuotient,
    `SerrePositivity.KST.Fibration.RelativeSimplicialDiagram,
    `SerrePositivity.KST.Fibration.SJointReflection,
    `SerrePositivity.KST.Fibration.SimplexFiberBaseChange,
    `SerrePositivity.KST.Fibration.SimplicialCylinderDiagonal,
    `SerrePositivity.KST.Fibration.StableZeroEndContraction,
    `SerrePositivity.KST.Fibration.StableZeroSContraction,
    `SerrePositivity.KST.Fibration.StableZeroSDiagonalCylinder,
    `SerrePositivity.KST.Fibration.StableZeroSPoint,
    `SerrePositivity.KST.Fibration.StandardJoinTailFace,
    `SerrePositivity.KST.Fibration.StandardTailAttachment,
    `SerrePositivity.KST.Fibration.StandardTailCoordinates,
    `SerrePositivity.KST.Fibration.StandardTailVertices,
    `SerrePositivity.KST.Fibration.TailAttachment,
    `SerrePositivity.KST.Fibration.TailRelativeCompletion,
    `SerrePositivity.KST.Fibration.TailWeakEndpoint,
    `SerrePositivity.KST.Fibration.TailWeakJointReflection,
    `SerrePositivity.KST.Fibration.TailWeakModel,
    `SerrePositivity.KST.Fibration.TailWeakMultiStep,
    `SerrePositivity.KST.Fibration.TailWeakPullback,
    `SerrePositivity.KST.Fibration.TailWeakReflection,
    `SerrePositivity.KST.Fibration.TopClosedStableIso,
    `SerrePositivity.KST.Fibration.TopPostcomposition,
    `SerrePositivity.KST.Fibration.WeakArrowAdditivity,
    `SerrePositivity.KST.Fibration.WeakArrowAmbientExact,
    `SerrePositivity.KST.Fibration.WeakArrowCategory,
    `SerrePositivity.KST.Fibration.WeakArrowClosedPredicate,
    `SerrePositivity.KST.Fibration.WeakArrowEndpointExact,
    `SerrePositivity.KST.Fibration.WeakArrowEquivalence,
    `SerrePositivity.KST.Fibration.WeakCofiberCompletion,
    `SerrePositivity.KST.Fibration.WeakCofiberCompletionSection,
    `SerrePositivity.KST.Fibration.WeakCofiberVertices,
    `SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.WeakEquivalences,
    `SerrePositivity.KST.Fibration.WeakStringCofiberFamilies,
    `SerrePositivity.KST.Fibration.WeakStringCofiberRealization,
    `SerrePositivity.KST.Fibration.WeakStringCofiberSource,
    `SerrePositivity.KST.Fibration.WeakStringCofiberVertices,
    `SerrePositivity.KST.Fibration.WeakStringCofibers,
    `SerrePositivity.KST.Fibration.WeakStringConstantNaturality,
    `SerrePositivity.KST.Fibration.WeakStringConstantPostcomposition,
    `SerrePositivity.KST.Fibration.WeakStringConstants,
    `SerrePositivity.KST.Fibration.WeakStringEdges,
    `SerrePositivity.KST.Fibration.WeakStringFiniteAllLengths,
    `SerrePositivity.KST.Fibration.WeakStringFiniteComparison,
    `SerrePositivity.KST.Fibration.WeakStringFiniteComparisonOne,
    `SerrePositivity.KST.Fibration.WeakStringFiniteEquivalence,
    `SerrePositivity.KST.Fibration.WeakStringFiniteRecursion,
    `SerrePositivity.KST.Fibration.WeakStringGappedNaturality,
    `SerrePositivity.KST.Fibration.WeakStringGappedTranspose,
    `SerrePositivity.KST.Fibration.WeakStringGappedVerticesEquiv,
    `SerrePositivity.KST.Fibration.WeakStringObjectRelativeIso,
    `SerrePositivity.KST.Fibration.WeakStringOneEquivalence,
    `SerrePositivity.KST.Fibration.WeakStringPostNaturality,
    `SerrePositivity.KST.Fibration.WeakStringPostcomposition,
    `SerrePositivity.KST.Fibration.WeakStringRealizationConstants,
    `SerrePositivity.KST.Fibration.WeakStringRelativeCoreRealization,
    `SerrePositivity.KST.Fibration.WeakStringRelativeDiagonal,
    `SerrePositivity.KST.Fibration.WeakStringTailCanonicalComponents,
    `SerrePositivity.KST.Fibration.WeakStringTailComponents,
    `SerrePositivity.KST.Fibration.WeakStringTailEquivalence,
    `SerrePositivity.KST.Fibration.WeakStringTailMultiStep,
    `SerrePositivity.KST.Fibration.WeakStringTwoCriterion,
    `SerrePositivity.KST.Fibration.WeakStringTwoHornComponents,
    `SerrePositivity.KST.Fibration.WeakStringTwoHornEquivalence,
    `SerrePositivity.KST.Fibration.WeakStringVertexPostcomposition,
    `SerrePositivity.KST.Fibration.WeakStringVertices,
    `SerrePositivity.KST.Fibration.WeakStringZeroEquivalence,
    `SerrePositivity.KST.Fibration.WeakStringZeroRow,
    `SerrePositivity.KST.Fibration.WeakStrings,
    `SerrePositivity.KST.Fibration.WeakStringsExact,
    `SerrePositivity.KST.Fibration.WeakStringsSimplicial,
    `SerrePositivity.KST.Fibration.WeakStringsStability]
  for m in env.header.modules do
    if ((`SerrePositivity.KST.Fibration).isPrefixOf m.module &&
        !approvedRelativeClosure.contains m.module) ||
        (`SerrePositivity.KST.NonConnective).isPrefixOf m.module then
      throwError "K-cof: reverse dependency on K-B: {m.module}"
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless owner.isPrefixOf mod do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "K-cof: ModelCategory in type of {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "K-cof: unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if count == 0 then throwError "K-cof: no declarations audited"
  for mod in expected do
    unless modules.contains mod do throwError "K-cof: required module missing: {mod}"
  logInfo m!"K-cof: {count} declarations in {modules.size} modules; standard axioms only."

#check @SerrePositivity.KST.SConstruction.Cofinality.completion_isEssentiallySurjective_of_complete_source
#check @SerrePositivity.KST.SConstruction.Cofinality.completion_isQCatEquivalence_of_complete_source
#check @SerrePositivity.KST.SConstruction.Cofinality.completionStableEquivalenceOfCompleteSource
#check @SerrePositivity.KST.SConstruction.Cofinality.kSpectrumMap_piIsomorphism_of_complete_source
#check @SerrePositivity.KST.SConstruction.Cofinality.sEndofunctor_map_isFullyFaithful
#check @SerrePositivity.KST.SConstruction.Cofinality.multiSEndofunctor_map_isFullyFaithful
#check @SerrePositivity.KST.SConstruction.Cofinality.kSpectrumMap_zero_injective_iff
#check @SerrePositivity.KST.SConstruction.Cofinality.exists_sFamily_of_pointwise_image
#check @SerrePositivity.KST.SConstruction.Cofinality.exists_multiSFamily_of_pointwise_image
#check @SerrePositivity.KST.SConstruction.Cofinality.sBiprodShift_mem_image_of_density
#check @SerrePositivity.KST.SConstruction.Cofinality.kSpectrumMap_cofinality_iff_boundary
#check @SerrePositivity.KST.SConstruction.Cofinality.sBoundaryRecoveryIso_postcomp
#check @SerrePositivity.KST.SConstruction.Cofinality.multiSBiprodShift_mem_image_of_completion
#check @SerrePositivity.KST.SConstruction.Cofinality.exists_multiSFamily_of_biprodShift

#check @SerrePositivity.KST.SConstruction.Cofinality.multiSEndofunctor_map_isIdempotentCompletion
#check @SerrePositivity.KST.SConstruction.Cofinality.stableWideCofinalitySupply_of_api
#check @SerrePositivity.KST.SConstruction.Cofinality.multiWideStageDiagram
#check @SerrePositivity.KST.SConstruction.Cofinality.suppliedMultiRelativeFlagDiagram
#check @SerrePositivity.KST.SConstruction.Cofinality.multiRelativeFlagZeroIso
#check @SerrePositivity.KST.SConstruction.Cofinality.suppliedMultiRelativeFlagsMap_zero
#check @SerrePositivity.KST.SConstruction.Cofinality.multiSourceToRelativeFlags_zero

#check @SerrePositivity.KST.SConstruction.Cofinality.stableWideCofinalitySupply
#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeFlagDiagram
#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeFlagWideEvaluation
#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeFlagEvaluation_zero
#check @SerrePositivity.KST.SConstruction.Cofinality.completionMultiWide_componentRetraction
#check @SerrePositivity.KST.SConstruction.Cofinality.completionMultiWideComponent_image_iff
#check @SerrePositivity.KST.SConstruction.Cofinality.exists_multiSourceFamily_of_relative_component

#check @SerrePositivity.KST.SConstruction.Cofinality.exists_completionSourceFlagVertexIso
#check @SerrePositivity.KST.SConstruction.Cofinality.completionSourceFlagVertexImage_iff
#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeImageFlagEquivalence
#check @SerrePositivity.KST.SConstruction.Cofinality.completionSourceImageFlagMap_core_isQCatEquivalence

#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeFlagEvaluation_eq_diagonalRestriction
#check @SerrePositivity.KST.SConstruction.Cofinality.completionWideFlagDiagonalComparison_evaluation
#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeFlagWideEvaluation_isWeak_of_coreFlag
#check @SerrePositivity.KST.SConstruction.Cofinality.completionWide_invertibleEdge_of_ambient
#check @SerrePositivity.KST.SConstruction.Cofinality.completionWideRelativeCoreIso
#check @SerrePositivity.KST.SConstruction.Cofinality.completionWideFlagDiagonalComparison_isWeak
#check @SerrePositivity.KST.SConstruction.Cofinality.CompletionCoreFlagEvaluationInput
#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeFlagWideEvaluation_isWeak_of_input
#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeFlag_positive_subsingleton_of_input
#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeFlag_recovery_iff_imageComponent
#check @SerrePositivity.KST.SConstruction.Cofinality.completionWideImageComponent_iff_basepoint
#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeFlag_recovery_iff_basepoint
#check @SerrePositivity.KST.SConstruction.Cofinality.completionImageClosedPredicate
#check @SerrePositivity.KST.SConstruction.Cofinality.completionSourceImageStableEquivalence
#check @SerrePositivity.KST.SConstruction.Cofinality.completionSourceImageStableMap_inclusion
#check @SerrePositivity.KST.SConstruction.Cofinality.completionImageSStableIso
#check @SerrePositivity.KST.SConstruction.Cofinality.completionImage_multiPointwise_iff
#check @SerrePositivity.KST.SConstruction.Cofinality.completionSourceImageNatTrans
#check @SerrePositivity.KST.SConstruction.Cofinality.completionK_bijective_iff_imageInclusion
#check @SerrePositivity.KST.SConstruction.Cofinality.completionK_injective_iff_imageInclusion
#check @SerrePositivity.KST.SConstruction.Cofinality.completionWideKZeroObstruction
#check @SerrePositivity.KST.SConstruction.Cofinality.completionWideKZeroObstruction_surjective
#check @SerrePositivity.KST.SConstruction.Cofinality.completionWideAddCommGroup
#check @SerrePositivity.KST.SConstruction.Cofinality.completionWideTriangle_additivity
#check @SerrePositivity.KST.SConstruction.Cofinality.completionKZeroCokernelToWide_leftInverse
#check @SerrePositivity.KST.SConstruction.Cofinality.completionWideKZeroObstruction_bijective
#check @SerrePositivity.KST.SConstruction.Cofinality.completionWideKZeroObstructionEquiv
#check @SerrePositivity.KST.SConstruction.Cofinality.completionKZeroCokernelStructureMap
#check @SerrePositivity.KST.SConstruction.Cofinality.completionCanonicalWideStructureMap_obstruction
#check @SerrePositivity.KST.SConstruction.Cofinality.completionWideGroupStructureMap_apply
#check @SerrePositivity.KST.SConstruction.Cofinality.completionKZeroCokernelDiagram
#check @SerrePositivity.KST.SConstruction.Cofinality.completionWideComponentCokernelNatIso

#check @SerrePositivity.KST.SConstruction.Cofinality.cutKZero_interval_decomposition
#check @SerrePositivity.KST.SConstruction.Cofinality.cutKZeroEquiv
#check @SerrePositivity.KST.SConstruction.Cofinality.cutCokernelEquiv
#check @SerrePositivity.KST.SConstruction.Cofinality.cutCokernelEquiv_apply

#check @SerrePositivity.KST.SConstruction.Cofinality.cutCokernelBarIso
#check @SerrePositivity.KST.SConstruction.Cofinality.cutCokernel_higher_of_input

#check @SerrePositivity.KST.SConstruction.Cofinality.completionWideHead_higher_of_input
#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeHead_higher_of_input

#check @SerrePositivity.KST.SConstruction.Cofinality.completionClosedFlagPredicate_iff

#check @SerrePositivity.KST.SConstruction.Cofinality.completionClosedFlagStableIso
#check @SerrePositivity.KST.SConstruction.Cofinality.completionSWideEdge_iff_pointwise

#check @SerrePositivity.KST.SConstruction.Cofinality.completionCoreFlagEvaluationInput
#check @SerrePositivity.KST.SConstruction.Cofinality.groupNerveHigherVanishingInput
#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeHead_higher_subsingleton

#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeSTranspose

#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeSInterchangeIso

#check @SerrePositivity.KST.SConstruction.Cofinality.completionClosedSFlagIso

#check @SerrePositivity.KST.SConstruction.Cofinality.completionClosedRelativeRealizationIso

#check @SerrePositivity.KST.SConstruction.Cofinality.completionClosedRelative_higher_subsingleton

#check @SerrePositivity.KST.SConstruction.Cofinality.completionClosedRelativeExInfinity_higher_subsingleton

#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeKanComparison_piIsomorphism_of_input

#check @SerrePositivity.KST.SConstruction.Cofinality.KanPullbackCofinalityInput

#check @SerrePositivity.KST.SConstruction.Cofinality.completionRelativeKanInclusion_groupConditions_of_inputs

#check @SerrePositivity.KST.SConstruction.Cofinality.kSpectrumMap_cofinality_of_inputs

#check @SerrePositivity.KST.SConstruction.Cofinality.kSpectrumMap_cofinality_of_relativeFiber_input


-- K-B3 が消費する公開型全体を固定する。追加の供給・instance 引数を許さない。
universe u
example : ∀ (X Y : SerrePositivity.KST.SConstruction.StableModel.{u}) (f : X ⟶ Y),
    SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective
        (SerrePositivity.KST.Spectra.OmegaSpectrum.homotopyMap
          (SerrePositivity.KST.SConstruction.kSpectrumMap f) j)) ∧
      Function.Injective (SerrePositivity.KST.Spectra.OmegaSpectrum.homotopyMap
        (SerrePositivity.KST.SConstruction.kSpectrumMap f) 0) :=
  fun _ _ f hf => SerrePositivity.KST.SConstruction.Cofinality.kSpectrumMap_cofinality f hf

open Lean in
run_cmd do
  let env ← getEnv
  let mut pending := [``SerrePositivity.KST.SConstruction.Cofinality.kSpectrumMap_cofinality]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if name == `SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence ||
        name == `HomotopicalAlgebra.ModelCategory then
      throwError "K-cof: forbidden proof dependency: {name}"
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.modules[idx.toNat]!.module
      if mod == `SerrePositivity.KST.Fibration.VerdierKernelEquivalence ||
          (`SerrePositivity.KST.NonConnective).isPrefixOf mod then
        throwError "K-cof: forbidden proof module: {mod} ({name})"
    if let some info := env.find? name then
      pending := info.type.getUsedConstants.toList ++ pending
      if let .inductInfo value := info then
        pending := value.ctors ++ pending
      if let some value := info.value? (allowOpaque := true) then
        pending := value.getUsedConstants.toList ++ pending
  logInfo m!"K-cof: unconditional theorem proof closure checked ({seen.size} constants)."

#check @SerrePositivity.KST.SConstruction.Cofinality.kSpectrumMap_cofinality
#print axioms SerrePositivity.KST.SConstruction.Cofinality.kSpectrumMap_cofinality
