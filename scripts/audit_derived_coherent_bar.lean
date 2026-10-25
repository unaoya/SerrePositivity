import SerrePositivity.InfinityCategories.Derived.CoherentBar.All
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
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Module,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.HomDegrees,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.HomEquations,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeDegeneracy,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.RawInclusions,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedGraded,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.DegeneracyOperators,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.EndRebase,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.LabelNormalization,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizationStages,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateSplitting,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedHomotopyImage,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateFaces,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateCuts,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.DegeneratePrefixCoefficients,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateFaceCoefficients,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateUnit,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.PositiveDegenerateFaceSum,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateUnitCoefficients,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.PositiveDegenerateColumn,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.ZeroDegenerateColumn,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateInvariant,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedHomFactorization,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.MaurerCartanDescent,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.MaurerCartanMap,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedProjection,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.HomFiltration,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.FiltrationColumns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.LabelNormalizationRecurrence,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.BoundaryFiltration,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.EndRebaseAlgebra,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.GradedStages,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.GradedStabilization,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CycleAlgebra,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StageComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.EndRebaseInjective,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.TwistedEndDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StabilizedEndomorphism,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.HomotopyStabilization,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.AccumulatedHomotopyEquation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StableHomotopyEquation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.Unconditional,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StableHomotopyImage,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.StableProjectionCompatibility,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.LabelVertexSupport,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedHomDegrees,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedTargetHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeColumns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedHomEquations,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.LastPostcomposition,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedTargetProjection,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeSimplexData,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeSimplices,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeLabelCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.SubsetPartialNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.BianchiLabelPartialNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeSimplexNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeCocone,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.ShiftedHomCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedNativeHomCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeHomComposition,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeHomUniversalColumns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeCoordinateNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeDegenerateColumns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeSubsetCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.LastPostcompositionResidual,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeHomCandidate,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeHomRestoration,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeFullCoefficient,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeUniversalMap,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeUniversalMapUnique,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyDegeneracies,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterDegeneracies,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinMixedIndex,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyMixedHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.FullSimplexRhs,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinSplitIndex,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.FullSimplexSigns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinCoordinateCases,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyPureHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinCuts,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeSubsetHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyFactorization,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.PostcompositionAlgebra,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.FullSimplexComponents,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinPointIndex,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeSourceErase,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeSourceLeftCut,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeSourceRightCut,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeSourceTerm,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeSourceSum,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterFaces,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterErase,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterRightCut,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterLeftCut,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.FullSimplexComposite,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterComposite,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterTerm,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.ParameterBoundarySum,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterSum,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyResidual,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyBoundary,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyHomDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.ParameterSubsetLabels,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLinearData,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLinearNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLinearFullCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLinearFullEquation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLinearEquation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeHomSpaceComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinSimplexDataExt,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLinearRecovery,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyExt,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterCoefficients,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinMixedEndpoints,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseMixedColumns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinRawGluing,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinRawCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawData,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinRawPureCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinRawRestrictions,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterRecovery,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseMixedRecovery,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawRecovery,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawFactorization,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseNativeFactorization,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawFaces,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawPureHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseSourceLeftCut,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseSourceErase,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseSourceRightCut,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseSourceTerm,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseSourceSum,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterFaces,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawRightHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterErase,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterLeftCut,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterRightCut,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterComposite,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterTerm,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterSum,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseBoundaryColumns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseFullDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseFullCoefficient,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseFullEquation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseMixedNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawFaceNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawMixedNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseEquationTransfer,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseSimplices,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinPartialInjectivity,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawPartialNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawVanishing,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseOverSection,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseCoconeFamily,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeHomSpaceInverse,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseCoconeHomRecovery,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeHomSpaceIso,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeColimitCosliceCriterion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeHomSpaceEquivalence,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeColimitPointHomCriterion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeCoconeFamily,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftDegeneracies,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftDifferential,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftMixedHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftFactorization,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftPureHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSourceErase,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSourceLeftCut,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSourceRightCut,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSourceTerm,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSourceSum,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftResidual,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftHomComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.PointHomLiftCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.LinearReflectionSigns,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.LinearReflectionData,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.LinearReflectionNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.LinearReflectionIso,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.LeftRightHomIso,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSubset,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.LeftRightHomCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSubsetFactorization,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftParameterData,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativePointHomLift,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftParameterErase,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftParameterLeftCut,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftParameterRightCut,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftParameterTerm,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftHomEquation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredParameterLeft,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredRightHom,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredParameterRight,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredParameterTerm,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredFullEquation,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftParameterDegeneracies,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftSubsetNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredFaceNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredMixedNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredVanishing,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredNaturality,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredSimplices,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconePointComparison,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconePointComparisonIdentity,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.PinchedTopCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconePointFiberCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.LeftRightTopCoordinates,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.PointHomSpaceIso,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconePointFiberIso,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.PointHomFamilyFiberCriterion,
    `SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeColimit]
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

#check SerrePositivity.InfinityCategories.dgCoherentBarModule
#check SerrePositivity.InfinityCategories.dgCoherentBarHomDegreeEquiv
#check SerrePositivity.InfinityCategories.dgCoherentBarHomDegreeEquiv_d
#check SerrePositivity.InfinityCategories.dgCoherentBarHomColumnsEquiv
#check SerrePositivity.InfinityCategories.dgCoherentBarClosedColumnsEquiv
#check SerrePositivity.InfinityCategories.dgCoherentBar_native_degenerateTriangle
#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizationStageHomotopy
#check SerrePositivity.InfinityCategories.dgCoherentBarLabelNormalizedEquiv
#check SerrePositivity.InfinityCategories.dgCoherentBarEndRebase_d
#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizedModule

#check SerrePositivity.InfinityCategories.dgCoherentBarCoconeHomSpaceIso
#check SerrePositivity.InfinityCategories.dgCoherentBarCoconeHomSpaceIsoUnconditional
#check SerrePositivity.InfinityCategories.dgCoherentBarCoconeHomSpaceComparison_homotopyEquivalence
#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizedNativeCocone_isColimit_of_cosliceComparison
#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizedNativeCocone_isColimit_of_pointHomComparison
#check SerrePositivity.InfinityCategories.dgCoherentBarNativeCoconePoint_hom

#check SerrePositivity.InfinityCategories.dgCoherentBarNativeLeftRightHomIso
#check SerrePositivity.InfinityCategories.dgCoherentBarLeftRightHomIso_component

#check SerrePositivity.InfinityCategories.dgCoherentBarNativePointHomLiftSimplex_source_hom
#check SerrePositivity.InfinityCategories.dgCoherentBarNativePointHomLiftSimplex_tail_hom
#check SerrePositivity.InfinityCategories.dgCoherentBarCoconeLiftHom_parameter_differential

#check SerrePositivity.InfinityCategories.dgCoherentBarCoconeRecoveredRawData_full_equation

#check SerrePositivity.InfinityCategories.dgCoherentBarCoconePointFiberIso

#check SerrePositivity.InfinityCategories.dgCoherentBarCoconePointFiber_comparison

#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizedNativeCocone_pointHomComparison_homotopyEquivalence

#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizedNativeCoconeUnconditional_isColimit

#check SerrePositivity.InfinityCategories.dgCoherentBarNormalizedNativeCoconeUnconditional_pointHomComparison_homotopyEquivalence
