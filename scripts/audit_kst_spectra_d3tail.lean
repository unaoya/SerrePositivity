import SerrePositivity.KST.Spectra.D3TailAll
import Lean.Util.CollectAxioms

/-!
概要：Sp-2b 専用集約と B を明示引数に持つ公開界面の監査。
方針：私有宣言も元モジュールから列挙し、推移的公理依存と宣言型を検査する。
規約：B の存在・無条件版の安定性を認証しない。独立した専用集約だけを import。
使われ方：d3c・d3d の保存検証。
-/

open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
open OmegaSpectrum.AdjointLoopRelativeBF
universe u

-- B 以外の仮定を持たず、元の nativeLoop と元の Sp を結論する型を検査。
example : (hB : NativeLoopComparison.{u}) → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence nativeLoop.{u} :=
  nativeLoop_isQCatEquivalence_of_tailComparison
example : (hB : NativeLoopComparison.{u}) → _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Sp.{u} := sp_isStable
#check @nativeLoop_isQCatEquivalence_of_tailComparison
#check @sp_isStable

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  for mod in env.header.modules do
    if (`SerrePositivity.KST.Fibration).isPrefixOf mod.module ||
        (`SerrePositivity.KST.LocalizingInvariants).isPrefixOf mod.module then
      throwError "Sp-2b d3tail: downstream K dependency imported: {mod.module}"
  for mod in #[
      `SerrePositivity.KST.Spectra.D3All] do
    if env.header.modules.any (·.module == mod) then
      throwError "Sp-2b d3tail: separate aggregate or disconnected leaf imported: {mod}"
  let expected := #[
    `SerrePositivity.KST.Spectra.D3ComparisonOutput,
    `SerrePositivity.KST.Spectra.D3TailLoopEquivalence,
    `SerrePositivity.KST.Spectra.D3TailStability,
    `SerrePositivity.KST.Spectra.SpectrumFiniteLimits,
    `SerrePositivity.KST.Spectra.SpectrumZeroObject,
    `SerrePositivity.KST.Spectra.SpectrumTailEquivalence]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.KST.Spectra).isPrefixOf mod do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "Sp-2b d3tail: ModelCategory assumption in type of {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Sp-2b d3tail: unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if count == 0 then throwError "Sp-2b d3tail: no declarations audited"
  for mod in expected do
    unless modules.contains mod do throwError "Sp-2b d3tail: required module missing: {mod}"
  logInfo m!"Sp-2b d3tail: {count} declarations in {modules.size} modules audited; standard three axioms only; B remains explicit."
