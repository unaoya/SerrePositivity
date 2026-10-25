import SerrePositivity.InfinityCategories.F2.Presentable.Supply.All
import Lean.Util.CollectAxioms

/-!
概要：P-s の供給宣言を公理監査する。
方針：宣言の所属モジュールを調べ、再帰的な公理依存を検査する。
規約：許す公理は propext・Classical.choice・Quot.sound のみ。
使われ方：Supply.All の対象ビルド後に lake env lean で実行する。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.InfinityCategories.F2.Presentable.Supply |>.isPrefixOf mod) do
      continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Presentable supply: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Presentable supply: no declarations audited"
  logInfo m!"Presentable supply audit passed: {count} declarations, standard three axioms only."

#check @SerrePositivity.InfinityCategories.F2.Presentable.hasPreservedColimit_iff_rightCofinalRestriction
#check @SerrePositivity.InfinityCategories.F2.Presentable.hasPreservedColimit_of_localLeftKan
#check @SerrePositivity.InfinityCategories.F2.Presentable.sequentialTelescopeShape
#check @SerrePositivity.InfinityCategories.F2.Presentable.sequentialTelescopeToNerve
#check @SerrePositivity.InfinityCategories.F2.Presentable.discreteProductNerveCofan_isColimit
#check @SerrePositivity.InfinityCategories.F2.Presentable.sequentialTelescopeFinalVertices_isRightCofinal
#check @SerrePositivity.InfinityCategories.F2.Presentable.hasPreservedColimit_sequentialTelescopeIntervals
#check @SerrePositivity.InfinityCategories.F2.Presentable.hasPreservedColimit_sequentialTelescopeShape
#check @SerrePositivity.InfinityCategories.F2.Presentable.sequentialNerveSupportEquiv
#check @SerrePositivity.InfinityCategories.F2.Presentable.sequentialSpinePairing
#check @SerrePositivity.InfinityCategories.F2.Presentable.sequentialSpine_inclusion_innerAnodyne
#check @SerrePositivity.InfinityCategories.F2.Presentable.sequentialTelescopeToSpine_isIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.sequentialTelescopeToNerve_innerAnodyne
#check @SerrePositivity.InfinityCategories.F2.Presentable.hasPreservedColimit_sequential_of_coproducts_finite
#check @SerrePositivity.InfinityCategories.F2.Presentable.preservesSequentialColimits_of_coproducts_finite
#check @SerrePositivity.InfinityCategories.F2.Presentable.hasPreservedColimit_smallCoproduct
#check @SerrePositivity.InfinityCategories.F2.Presentable.hasPreservedColimit_of_coproducts_preservedRealizations
#check @SerrePositivity.InfinityCategories.F2.Presentable.isKappaSmall_twistedArrow
#check @SerrePositivity.InfinityCategories.F2.Presentable.countable_geometricRealizationShape_simplices
#check @SerrePositivity.InfinityCategories.F2.Presentable.countableFiniteStage_finite
#check @SerrePositivity.InfinityCategories.F2.Presentable.iSup_countableFiniteStage
#check @SerrePositivity.InfinityCategories.F2.Presentable.countableSimplexStage_le_iff
#check @SerrePositivity.InfinityCategories.F2.Presentable.countableStageCommaEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.countableStageSimplexToComma_proj
#check @SerrePositivity.InfinityCategories.F2.Presentable.countableFiniteStageCocone_isColimit
#check @SerrePositivity.InfinityCategories.F2.Presentable.hasPreservedColimit_iff_lastVertexRestriction
#check @SerrePositivity.InfinityCategories.F2.Presentable.oppositeSimplexRestriction_naturality
#check @SerrePositivity.InfinityCategories.F2.Presentable.countableStageKanComparison_projection
#check @SerrePositivity.InfinityCategories.F2.Presentable.hasPreservedColimit_countableStage_leftKan
#check @SerrePositivity.InfinityCategories.F2.Presentable.hasPreservedColimit_countable_of_coproducts_finite
#check @SerrePositivity.InfinityCategories.F2.Presentable.hasPreservedColimit_of_coproducts_finite
#check @SerrePositivity.InfinityCategories.F2.Presentable.preservesSmallColimits_of_coproducts_finite
