import SerrePositivity.KST.SConstruction.Cofinality
import Lean.Util.CollectAxioms

/-!
概要：K-cof 所有葉の全宣言と推移的公理依存を監査する。
方針：実 import 元で所有宣言を列挙し、標準三公理だけであることを強制する。
規約：主経路の ModelCategory 型仮定、K-B 所有モジュールへの逆依存を拒否する。
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
    `SerrePositivity.KST.SConstruction.Cofinality.RelativeCoreFlagIso]
  for m in env.header.modules do
    if (`SerrePositivity.KST.Fibration).isPrefixOf m.module ||
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
