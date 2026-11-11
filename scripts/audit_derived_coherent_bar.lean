import SerrePositivity.InfinityCategories.Project.Entrypoints.DerivedCoherentBarAll
import Lean

/-!
概要：D-bar の所有葉の全宣言の公理依存を検査する。
方針：環境の所属モジュールで選別し、標準三公理のみを許容する。
規約：D の既存集約・既存監査を変更しない。
使われ方：自分の All のビルド後に lake env lean で実行する。
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Module,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.HomDegrees,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.HomEquations,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeDegeneracy,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.RawInclusions,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedGraded,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegeneracyOperators,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.EndRebase,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LabelNormalization,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizationStages,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateSplitting,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedHomotopyImage,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateFaces,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateCuts,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegeneratePrefixCoefficients,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateFaceCoefficients,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateUnit,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PositiveDegenerateFaceSum,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateUnitCoefficients,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PositiveDegenerateColumn,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ZeroDegenerateColumn,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateInvariant,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedHomFactorization,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.MaurerCartanDescent,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedDifferential,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.MaurerCartanMap,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedProjection,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.HomFiltration,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.FiltrationColumns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LabelNormalizationRecurrence,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.BoundaryFiltration,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.EndRebaseAlgebra,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.GradedStages,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.GradedStabilization,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CycleAlgebra,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StageComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.EndRebaseInjective,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.TwistedEndDifferential,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StabilizedEndomorphism,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.HomotopyStabilization,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.AccumulatedHomotopyEquation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StableHomotopyEquation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Unconditional,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StableHomotopyImage,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StableProjectionCompatibility,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LabelVertexSupport,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedHomDegrees,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedTargetHom,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeColumns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedHomEquations,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LastPostcomposition,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedTargetProjection,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeSimplexData,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeSimplices,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeLabelCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.SubsetPartialNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.BianchiLabelPartialNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeSimplexNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeCocone,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ShiftedHomCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedNativeHomCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeHomComposition,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeHomUniversalColumns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeCoordinateNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeDegenerateColumns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeSubsetCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LastPostcompositionResidual,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeHomCandidate,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeHomRestoration,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeFullCoefficient,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeUniversalMap,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeUniversalMapUnique,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyHom,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyDegeneracies,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeParameterDegeneracies,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinMixedIndex,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyDifferential,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyMixedHom,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.FullSimplexRhs,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinSplitIndex,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.FullSimplexSigns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinCoordinateCases,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyPureHom,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinCuts,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeSubsetHom,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyFactorization,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PostcompositionAlgebra,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.FullSimplexComponents,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinPointIndex,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeSourceErase,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeSourceLeftCut,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeSourceRightCut,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeSourceTerm,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeSourceSum,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeParameterFaces,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeParameterErase,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeParameterRightCut,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeParameterLeftCut,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.FullSimplexComposite,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeParameterComposite,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeParameterTerm,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ParameterBoundarySum,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeParameterSum,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyResidual,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyBoundary,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyHomDifferential,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ParameterSubsetLabels,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLinearData,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLinearNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLinearFullCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLinearFullEquation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLinearEquation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeHomSpaceComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinSimplexDataExt,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLinearRecovery,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyExt,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseParameterCoefficients,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinMixedEndpoints,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseMixedColumns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinRawGluing,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinRawCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseRawData,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinRawPureCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinRawRestrictions,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseParameterRecovery,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseMixedRecovery,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseRawRecovery,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseRawFactorization,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseNativeFactorization,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseRawFaces,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseRawPureHom,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseSourceLeftCut,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseSourceErase,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseSourceRightCut,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseSourceTerm,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseSourceSum,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseParameterFaces,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseRawRightHom,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseParameterErase,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseParameterLeftCut,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseParameterRightCut,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseParameterComposite,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseParameterTerm,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseParameterSum,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseBoundaryColumns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseFullDifferential,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseFullCoefficient,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseFullEquation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseMixedNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseRawFaceNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseRawMixedNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseEquationTransfer,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseSimplices,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinPartialInjectivity,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseRawPartialNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseRawVanishing,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseOverSection,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseCoconeFamily,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeHomSpaceInverse,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseCoconeHomRecovery,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeHomSpaceIso,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeColimitCosliceCriterion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeHomSpaceEquivalence,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeColimitPointHomCriterion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeCoconeFamily,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftHom,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftDegeneracies,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftDifferential,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftMixedHom,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftFactorization,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftPureHom,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftSourceErase,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftSourceLeftCut,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftSourceRightCut,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftSourceTerm,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftSourceSum,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftResidual,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftHomComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PointHomLiftCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LinearReflectionSigns,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LinearReflectionData,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LinearReflectionNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LinearReflectionIso,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LeftRightHomIso,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftSubset,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LeftRightHomCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftSubsetFactorization,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftParameterData,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativePointHomLift,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftParameterErase,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftParameterLeftCut,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftParameterRightCut,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftParameterTerm,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftHomEquation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredParameterLeft,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredRightHom,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredParameterRight,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredParameterTerm,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredFullEquation,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftParameterDegeneracies,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftSubsetNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredFaceNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredMixedNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredVanishing,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredNaturality,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredSimplices,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconePointComparison,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconePointComparisonIdentity,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PinchedTopCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconePointFiberCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LeftRightTopCoordinates,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PointHomSpaceIso,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconePointFiberIso,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PointHomFamilyFiberCriterion,
    `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeColimit]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"D-bar axiom audit passed: {count} declarations in {seen.size} modules."

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomDegreeEquiv
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomDegreeEquiv_d
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHomColumnsEquiv
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarClosedColumnsEquiv
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBar_native_degenerateTriangle
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationStageHomotopy
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelNormalizedEquiv
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarEndRebase_d
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeHomSpaceIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeHomSpaceIsoUnconditional
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeHomSpaceComparison_homotopyEquivalence
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCocone_isColimit_of_cosliceComparison
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCocone_isColimit_of_pointHomComparison
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeCoconePoint_hom

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeLeftRightHomIso
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLeftRightHomIso_component

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativePointHomLiftSimplex_source_hom
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativePointHomLiftSimplex_tail_hom
#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom_parameter_differential

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_full_equation

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconePointFiberIso

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconePointFiber_comparison

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCocone_pointHomComparison_homotopyEquivalence

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCoconeUnconditional_isColimit

#check SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCoconeUnconditional_pointHomComparison_homotopyEquivalence
