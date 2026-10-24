import SerrePositivity.KST.NonConnective
import Lean.Util.CollectAxioms

/-! K-7 所有モジュールの全宣言（私有・自動生成を含む）と推移的公理依存を監査する。 -/

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.KST.NonConnective.DGKappaSuspensionInputLaws,
    `SerrePositivity.KST.NonConnective.DGKappaSuspensionKMapLaws,

    `SerrePositivity.KST.NonConnective.DGKappaSuspensionKMap,
    `SerrePositivity.KST.NonConnective.DGKappaSuspensionKRoof,
    `SerrePositivity.KST.NonConnective.DGKappaSplitCofiberSupply,
    `SerrePositivity.KST.NonConnective.DGKappaConnectedKSwindle,
    `SerrePositivity.KST.NonConnective.DGKappaSplitKAdditivity,
    `SerrePositivity.KST.NonConnective.DGKappaSplitCofiberExact,
    `SerrePositivity.KST.NonConnective.DGKappaSplitCofiberEvaluations,
    `SerrePositivity.KST.NonConnective.DGKappaSplitCofiberFamily,
    `SerrePositivity.KST.NonConnective.DGKappaSplitModuleCells,
    `SerrePositivity.KST.NonConnective.DGKappaSplitModuleEvaluation,
    `SerrePositivity.KST.NonConnective.AdditivityGroupDecomposition,
    `SerrePositivity.KST.NonConnective.BoundaryAdditivity,
    `SerrePositivity.KST.NonConnective.CofiberAxes,
    `SerrePositivity.KST.NonConnective.ConnectedKMiddleAdditivity,
    `SerrePositivity.KST.NonConnective.DGClosedHomLinearity,
    `SerrePositivity.KST.NonConnective.DGFixedKAction,
    `SerrePositivity.KST.NonConnective.DGCountableSum,
    `SerrePositivity.KST.NonConnective.DGCountableSwindle,
    `SerrePositivity.KST.NonConnective.DGKappaConeInput,
    `SerrePositivity.KST.NonConnective.DGKappaFullPerfAction,
    `SerrePositivity.KST.NonConnective.DGKappaPerfClosedEdges,
    `SerrePositivity.KST.NonConnective.DGKappaPerfZeroFamily,
    `SerrePositivity.KST.NonConnective.DGKappaPerfectInput,
    `SerrePositivity.KST.NonConnective.DGKappaSplitInclusions,
    `SerrePositivity.KST.NonConnective.DGKappaSplitProjections,
    `SerrePositivity.KST.NonConnective.DGKappaSplitRelations,
    `SerrePositivity.KST.NonConnective.DGKappaSplitPerfRelations,
    `SerrePositivity.KST.NonConnective.DGKappaSplitPerfEvaluation,
    `SerrePositivity.KST.NonConnective.DGKappaSplitNativeSquare,
    `SerrePositivity.KST.NonConnective.DGKappaSplitPerfSquareCoordinates,
    `SerrePositivity.KST.NonConnective.DGKappaSuspension,
    `SerrePositivity.KST.NonConnective.DGKappaSwindle,
    `SerrePositivity.KST.NonConnective.DGKappaSwindleInfinity,
    `SerrePositivity.KST.NonConnective.DGKappaZeroFunctor,
    `SerrePositivity.KST.NonConnective.DGKappaZeroPerfAction,
    `SerrePositivity.KST.NonConnective.DGSumFamily,
    `SerrePositivity.KST.NonConnective.DGSumFamilyInclusion,
    `SerrePositivity.KST.NonConnective.DGSumPairProjection,
    `SerrePositivity.KST.NonConnective.DGSumPairSplit,
    `SerrePositivity.KST.NonConnective.DGSuspensionIteration,
    `SerrePositivity.KST.NonConnective.DGSwindleEnriched,
    `SerrePositivity.KST.NonConnective.DGSwindleFixedK,
    `SerrePositivity.KST.NonConnective.DGSwindleInputIso,
    `SerrePositivity.KST.NonConnective.DGSwindleStrict,
    `SerrePositivity.KST.NonConnective.FixedSpectrumAction,
    `SerrePositivity.KST.NonConnective.KanReplacementZero,
    `SerrePositivity.KST.NonConnective.NonnegativeBoundaryComparison,
    `SerrePositivity.KST.NonConnective.SequentialBFArrowFactorization,
    `SerrePositivity.KST.NonConnective.SequentialBFArrowStage,
    `SerrePositivity.KST.NonConnective.SequentialCandidateColimit,
    `SerrePositivity.KST.NonConnective.SequentialCandidateLegs,
    `SerrePositivity.KST.NonConnective.SequentialCandidatePi,
    `SerrePositivity.KST.NonConnective.SequentialCofibrantColimit,
    `SerrePositivity.KST.NonConnective.SequentialCoherentCocone,
    `SerrePositivity.KST.NonConnective.SequentialCoherentLift,
    `SerrePositivity.KST.NonConnective.SequentialColimit,
    `SerrePositivity.KST.NonConnective.SequentialColimitPi,
    `SerrePositivity.KST.NonConnective.SequentialComparison,
    `SerrePositivity.KST.NonConnective.SequentialConeComparison,
    `SerrePositivity.KST.NonConnective.SequentialDiagramReplacement,
    `SerrePositivity.KST.NonConnective.SequentialDiagramTransport,
    `SerrePositivity.KST.NonConnective.SequentialEdgePi,
    `SerrePositivity.KST.NonConnective.SequentialHomLimitCompatibility,
    `SerrePositivity.KST.NonConnective.SequentialHomStep,
    `SerrePositivity.KST.NonConnective.SequentialIndexFunctors,
    `SerrePositivity.KST.NonConnective.SequentialLatchingHom,
    `SerrePositivity.KST.NonConnective.SequentialLevelColimit,
    `SerrePositivity.KST.NonConnective.SequentialLevelColimitMap,
    `SerrePositivity.KST.NonConnective.SequentialLevelColimitUniversal,
    `SerrePositivity.KST.NonConnective.SequentialLevelHomLimit,
    `SerrePositivity.KST.NonConnective.SequentialNativeHomLimit,
    `SerrePositivity.KST.NonConnective.SequentialPi,
    `SerrePositivity.KST.NonConnective.SequentialPointedPushoutMono,
    `SerrePositivity.KST.NonConnective.SequentialRawHomDiagram,
    `SerrePositivity.KST.NonConnective.SequentialRawHomLimit,
    `SerrePositivity.KST.NonConnective.SequentialRelativeCofibration,
    `SerrePositivity.KST.NonConnective.SequentialRelativeHomFamily,
    `SerrePositivity.KST.NonConnective.SequentialRelativeHomFibration,
    `SerrePositivity.KST.NonConnective.SequentialRelativeHomNext,
    `SerrePositivity.KST.NonConnective.SequentialResizedDiagramIso,
    `SerrePositivity.KST.NonConnective.SequentialSpectrum,
    `SerrePositivity.KST.NonConnective.SequentialTowerIndex,
    `SerrePositivity.KST.NonConnective.SingleBoundaryMiddle,
    `SerrePositivity.KST.NonConnective.SingleRealizationZero,
    `SerrePositivity.KST.NonConnective.SwindleGroupCancellation]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.KST.NonConnective).isPrefixOf mod do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "K-7: ModelCategory assumption in type of {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "K-7: unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if count == 0 then throwError "K-7: no declarations audited"
  for mod in expected do
    unless modules.contains mod do throwError "K-7: required module missing: {mod}"
  logInfo m!"K-7: {count} declarations in {modules.size} modules audited; standard axioms only."

#check SerrePositivity.KST.NonConnective.sequentialPiCoconeIsColimit
#check SerrePositivity.KST.NonConnective.sequentialPiUnderlyingIsColimit
#check SerrePositivity.KST.NonConnective.sequentialPi_exists_late
#check SerrePositivity.KST.NonConnective.sequentialPi_eq_iff
#check SerrePositivity.KST.NonConnective.sequentialInjection_bijective_of_stable
#check SerrePositivity.KST.NonConnective.sequentialPi_subsingleton_iff
#check SerrePositivity.KST.NonConnective.sequentialPi_subsingleton_of_eventually
#check SerrePositivity.KST.NonConnective.sequentialInjection_bijective_on
#check SerrePositivity.KST.NonConnective.sequentialInjection_isInvertible_of_stable

#check SerrePositivity.KST.NonConnective.sequentialRawInjectionCone
#check SerrePositivity.KST.NonConnective.sequentialReflectedEndProjection_trivial
#check SerrePositivity.KST.NonConnective.sequentialReflectedBFInjectionPoint_projection
#check SerrePositivity.KST.NonConnective.sequentialCoherentCocone
#check SerrePositivity.KST.NonConnective.sequentialCoherentCocone_vertex

#check SerrePositivity.KST.NonConnective.sequentialKanSequence_sigma_mono
#check SerrePositivity.KST.NonConnective.sequentialLevelColimitIsColimit
#check SerrePositivity.KST.NonConnective.sequentialReplacementProjection_piIsomorphism

#check SerrePositivity.KST.NonConnective.sequentialLevelHomIsLimit
#check SerrePositivity.KST.NonConnective.sequentialHomLimitFamily_fac

#check SerrePositivity.KST.NonConnective.sequentialHomLimitFamily_condition
#check SerrePositivity.KST.NonConnective.sequentialRawHomLimitLift_fac
#check SerrePositivity.KST.NonConnective.sequentialRawHomIsLimit

#check SerrePositivity.KST.NonConnective.sequentialBFArrow_fac
#check SerrePositivity.KST.NonConnective.sequentialBFArrowRight_piIsomorphism
#check SerrePositivity.KST.NonConnective.sequentialBFArrowLeft_isRelativeCofibration
#check SerrePositivity.KST.NonConnective.sequentialRawHomPre_fibration
#check SerrePositivity.KST.NonConnective.sequentialDiagramReplacementComparison_piIsomorphism
#check SerrePositivity.KST.NonConnective.sequentialReplacementLevelCocone_isColimit
#check SerrePositivity.KST.NonConnective.sequentialSpColimitCocone_isColimit
#check SerrePositivity.KST.NonConnective.sequentialLevelColimitMap_piIsomorphism
#check SerrePositivity.KST.NonConnective.sequentialLevelColimitHomotopyIso_ι
#check SerrePositivity.KST.NonConnective.sequentialCandidateColimitCocone_isColimit
#check SerrePositivity.KST.NonConnective.sequentialCandidateColimitCocone_vertex
#check SerrePositivity.KST.NonConnective.sequentialCandidateColimitLeg_hom_eq
#check SerrePositivity.KST.NonConnective.sequentialCandidateColimitLeg_pi
#check SerrePositivity.KST.NonConnective.sequentialCandidatePiCoconeIsColimit
#check SerrePositivity.KST.NonConnective.sequentialCandidateColimitHomotopyIso_ι

#check SerrePositivity.KST.NonConnective.DGKappaConeInput
#check SerrePositivity.KST.NonConnective.DGKappaConeInput.derivedFullyFaithful
#check SerrePositivity.KST.NonConnective.DGKappaConeInput.kappaCompact
#check SerrePositivity.KST.NonConnective.DGKappaConeInput.covers
#check SerrePositivity.KST.NonConnective.DGKappaConeInput.countableClosed
#check SerrePositivity.KST.NonConnective.DGKappaPerfectInput
#check SerrePositivity.KST.NonConnective.DGKappaPerfectInput.inclusion
#check SerrePositivity.KST.NonConnective.dgCountableSumHom_injection
#check SerrePositivity.KST.NonConnective.dgCountableSumFunctor
#check SerrePositivity.KST.NonConnective.dgSwindleHom_enriched_naturality
#check SerrePositivity.KST.NonConnective.dgKappaConeCountableSum
#check SerrePositivity.KST.NonConnective.dgKappaSwindleStrictHom
#check SerrePositivity.KST.NonConnective.dgKappaSwindleStrictInv
#check SerrePositivity.KST.NonConnective.dgKappaSwindleComponentIso
#check SerrePositivity.KST.NonConnective.dgKappaSwindleInfinityIso
#check SerrePositivity.KST.NonConnective.dgKappaConeCountableSum_isExactFunctor
#check SerrePositivity.KST.NonConnective.dgKappaSuspension_isStableVerdierSequence
#check SerrePositivity.KST.NonConnective.dgKappaSuspensionKInput
#check SerrePositivity.KST.NonConnective.dgKappaSuspension_kills_perfect

#check SerrePositivity.KST.NonConnective.DGSuspensionStageProvider
#check SerrePositivity.KST.NonConnective.dgSuspensionIteration
#check SerrePositivity.KST.NonConnective.dgSuspensionIterationStage
#check SerrePositivity.KST.NonConnective.dgKappaSwindleClosedFunctorIso
#check SerrePositivity.KST.NonConnective.dgKappaSwindleNativeInputEdge
#check SerrePositivity.KST.NonConnective.dgKappaSwindleFixedK_pi
#check SerrePositivity.KST.NonConnective.boundaryKanAdditivityMap_piIsomorphism
#check SerrePositivity.KST.NonConnective.nonnegativeBoundaryEquiv_naturality
#check SerrePositivity.KST.NonConnective.connectedKMiddle_additivity
#check SerrePositivity.KST.NonConnective.dgKappaSplit_decomposition
#check SerrePositivity.KST.NonConnective.DGKappaZeroInput
#check SerrePositivity.KST.NonConnective.dgKappaZeroFunctor_isZero
#check SerrePositivity.KST.NonConnective.dgKappaZeroPerfAction_isZeroVertex
#check SerrePositivity.KST.NonConnective.dgKappaFullPerfFamilyMap_vertex
#check SerrePositivity.KST.NonConnective.dgKappaPerfClosedHomotopy
#check SerrePositivity.KST.NonConnective.dgKappaSplitPerfFamilySquare
