import SerrePositivity.KST.Descent
import Lean.Util.CollectAxioms

/-!
## 概要
主経路が条件付き補助の56モジュールを import しないことを監査する。
## 方針
実際の環境の import 閉包と全依存公理を検査し、公開型をログに残す。
## 規約
正本 §13 決定 15。最小公理全体と主定理全体の #check は完成時に追加する。
## 使われ方
論文 定理 3.1 の主経路を、補助結果の全体監査と分けて検査する。
-/

set_option pp.universes true in
#check SerrePositivity.KST.Descent.GradedPresheaf
#check SerrePositivity.KST.Descent.GradedPresheaf.PiDescent
#check SerrePositivity.KST.Descent.Nilinvariant
#check SerrePositivity.KST.Descent.NaturalBlowupSequences.sectioned_piDescent
#check SerrePositivity.KST.Descent.Main.totComparison
#check SerrePositivity.KST.Descent.Main.HasTotDescent
#check SerrePositivity.KST.Descent.Main.homotopyLimitComparison
#check SerrePositivity.KST.Descent.Main.weightedEndComparison
#check SerrePositivity.KST.Descent.Main.hasTotDescent_iff_of_stagewise_piIsomorphism

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[
    `SerrePositivity.KST.Descent.AugmentedCechRows,
    `SerrePositivity.KST.Descent.AugmentedCechSpaces,
    `SerrePositivity.KST.Descent.AugmentedCechWeightChange,
    `SerrePositivity.KST.Descent.AugmentedDerivedCechFubini,
    `SerrePositivity.KST.Descent.BottomSimplex,
    `SerrePositivity.KST.Descent.CechAdjointReindex,
    `SerrePositivity.KST.Descent.CechBaseLocality,
    `SerrePositivity.KST.Descent.CechDescentComparison,
    `SerrePositivity.KST.Descent.CechDescentRetract,
    `SerrePositivity.KST.Descent.CechFibrantDiagrams,
    `SerrePositivity.KST.Descent.CechFiniteProducts,
    `SerrePositivity.KST.Descent.CechLocalRanks,
    `SerrePositivity.KST.Descent.CechMapLocality,
    `SerrePositivity.KST.Descent.CechProductRestriction,
    `SerrePositivity.KST.Descent.CechRefinementDescent,
    `SerrePositivity.KST.Descent.CechReindexDescent,
    `SerrePositivity.KST.Descent.CechReindexLocalization,
    `SerrePositivity.KST.Descent.CechReindexWeights,
    `SerrePositivity.KST.Descent.CechWeakTransfer,
    `SerrePositivity.KST.Descent.ConstantCechDescent,
    `SerrePositivity.KST.Descent.DerivedCechFubini,
    `SerrePositivity.KST.Descent.DisjointFamilyCechWeak,
    `SerrePositivity.KST.Descent.DoubleAugmentedCechSpaces,
    `SerrePositivity.KST.Descent.DoubleCechDescent,
    `SerrePositivity.KST.Descent.DoubleCechDescentReflection,
    `SerrePositivity.KST.Descent.EmptyZariskiDescent,
    `SerrePositivity.KST.Descent.FamilyCechLocalRanks,
    `SerrePositivity.KST.Descent.FamilyCechMapLocality,
    `SerrePositivity.KST.Descent.FamilyCechOver,
    `SerrePositivity.KST.Descent.FamilyCechOverRanks,
    `SerrePositivity.KST.Descent.FiniteFreeChartFamilyRanks,
    `SerrePositivity.KST.Descent.FiniteFreeChartLocalRanks,
    `SerrePositivity.KST.Descent.InitialCechDescent,
    `SerrePositivity.KST.Descent.InitialCechWeights,
    `SerrePositivity.KST.Descent.IteratedCechHomotopyCones,
    `SerrePositivity.KST.Descent.MixedCechSpaces,
    `SerrePositivity.KST.Descent.OverRankCharts,
    `SerrePositivity.KST.Descent.PresheafCechSpaces,
    `SerrePositivity.KST.Descent.PresheafWeakTransfer,
    `SerrePositivity.KST.Descent.SplitCechDescent,
    `SerrePositivity.KST.Descent.SplitCechSpaceExtension,
    `SerrePositivity.KST.Descent.TerminalCechDescent,
    `SerrePositivity.KST.Descent.TransferBaseChangeComposite,
    `SerrePositivity.KST.Descent.TransferBaseChangeDescent,
    `SerrePositivity.KST.Descent.TransferCechDescent,
    `SerrePositivity.KST.Descent.TransferRankChartBaseChangeDescent,
    `SerrePositivity.KST.Descent.TransferRankChartDescent,
    `SerrePositivity.KST.Descent.TransferRankRefinementDescent,
    `SerrePositivity.KST.Descent.TransferWeakCechDescent,
    `SerrePositivity.KST.Descent.WeightedCechAugmentation,
    `SerrePositivity.KST.Descent.WeightedCechCofibrancy,
    `SerrePositivity.KST.Descent.WeightedCechDerivedComparison,
    `SerrePositivity.KST.Descent.WeightedCechDerivedConeCompatibility,
    `SerrePositivity.KST.Descent.WeightedCechDerivedFubini,
    `SerrePositivity.KST.Descent.ZariskiCechLaw,
    `SerrePositivity.KST.Descent.ZariskiCoproductDescent]
  for entry in env.header.modules do
    if (`SerrePositivity.Archive.KST.DescentConditional).isPrefixOf entry.module then
      throwError "Main route imported archived conditional auxiliary module: {entry.module}"
    if forbidden.contains entry.module then
      throwError "Main route imported conditional auxiliary module: {entry.module}"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.KST.Descent).isPrefixOf mod do continue
    let axioms ← collectAxioms name
    let bad := axioms.filter fun ax ↦ !(#[``propext, ``Classical.choice, ``Quot.sound].contains ax)
    unless bad.isEmpty do throwError "Unexpected axioms in {name}: {bad}"
    count := count + 1
  logInfo m!"Main route audit passed: {count} declarations; 56 conditional modules excluded."
  logInfo "Final minimal-law structure and full Theorem 3.1 are not yet constructed."
