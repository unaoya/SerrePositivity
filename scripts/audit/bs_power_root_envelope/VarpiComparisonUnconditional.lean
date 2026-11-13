module

import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.VarpiComparison
import Mathlib.Util.AssertNoSorry

/-!
# BS 著者版 Remark 7.15（著者版 p.62）：A1-c2 の専用監査

## 概要
公開五宣言と生成宣言の公理を検査し、旧 hpR 付き宣言への逆依存も拒否する。

## 方針
型と opaque 値を含む依存グラフを辿り、標準三公理だけを許可する。

## 規約
一般加群の還元判定の正則性仮定は保持する。旧名の import 自体は許す。

## 使われ方
無条件版への受渡しと引用・sorry の非追加の検収。
-/

-- 監査専用モジュールであり、公開定義は追加しない。
set_option linter.privateModule false
open SerrePositivity.BhattScholze
open SerrePositivity.BhattScholze.Andre.VarpiComparison

assert_no_sorry perfectPrismPDTensorVarpiDividedPowers_of_unconditional
assert_no_sorry perfectPrismPDTensorVarpiDividedPowers_generator_of_unconditional
assert_no_sorry perfectPrismPDTensorVarpi_isDPMorphism_of_unconditional
assert_no_sorry hodgeTate_completelyFaithfullyFlat_iff_of_unconditional
assert_no_sorry hodgeTate_coefficient_comparison_of_unconditional

#print axioms perfectPrismPDTensorVarpiDividedPowers_of_unconditional
#print axioms perfectPrismPDTensorVarpiDividedPowers_generator_of_unconditional
#print axioms perfectPrismPDTensorVarpi_isDPMorphism_of_unconditional
#print axioms hodgeTate_completelyFaithfullyFlat_iff_of_unconditional
#print axioms hodgeTate_coefficient_comparison_of_unconditional

-- 旧比較と同じ結論を保ち、hpR だけを除いていることを型検査する。
section Signature
open SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
example (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) (hf : f.Monic) :
    hodgeTate_completelyFaithfullyFlat_iff_of_unconditional W hW f hf =
      hodgeTate_completelyFaithfullyFlat_iff W hW f hpR hf := Subsingleton.elim _ _
example (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    hodgeTate_coefficient_comparison_of_unconditional W hW f hf hdeg =
      hodgeTate_coefficient_comparison W hW f hpR hf hdeg := Subsingleton.elim _ _
end Signature

meta section
open Lean Elab Command
open SerrePositivity.BhattScholze.Andre

/-- 概要：旧 hpR 付き宣言を経由していないことを型と値で検査する。
方針：公開宣言から依存を辿り、数学的公理は Lean 標準の収集器で検査する。
規約：既定タクティクの構文値は証明項と区別する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無条件版の依存監査。 -/
private partial def checkUnconditional (todo : List (Name × List Name))
    (seen : NameSet) : CoreM NameSet := do
  match todo with
  | [] => return seen
  | (n, path) :: rest =>
    if seen.contains n then return ← checkUnconditional rest seen
    let seen := seen.insert n
    let forbidden : Array Name := #[
      ``perfectPrismPDTensorVarpiDividedPowers,
      ``perfectPrismPDTensorVarpiDividedPowers_generator,
      ``perfectPrismPDTensorVarpi_isDPMorphism,
      ``hodgeTate_completelyFaithfullyFlat_iff,
      ``hodgeTate_coefficient_comparison,
      `SerrePositivity.BhattScholze.Andre.perfectPrismVarpiNativeDividedPowers,
      `SerrePositivity.BhattScholze.Andre.perfectPrismVarpiNativeDividedPowers_base_apply,
      `SerrePositivity.BhattScholze.Andre.perfectPrismVarpiPowerRootDividedPowers,
      `SerrePositivity.BhattScholze.Andre.perfectPrismVarpiPowerRootDividedPowers_base_apply,
      `SerrePositivity.BhattScholze.Andre.perfectPrismVarpiPowerRootDividedPowers_isDPMorphism,
      ``powerRootPrismMonicHodgeTate_varpi_regular]
    if forbidden.contains n then throwError "A1-c2：旧 hpR 宣言への依存 {n}"
    -- Lean 標準の collectAxioms と同じ kernel 環境で、非公開定義の仮の型を避ける。
    let some info := (← getEnv).checked.get.find? n |
      return ← checkUnconditional rest seen
    -- autoParam の既定タクティクは Syntax 値であり、証明項ではない。
    -- 論理的公理は別途 collectAxioms で全生成宣言について検査する。
    if info.type.isConstOf ``Syntax then return ← checkUnconditional rest seen
    match info with
    | .axiomInfo _ =>
      -- import 済み定理の不透明な型と実公理を標準の保存済み依存情報で区別する。
      let axioms ← collectAxioms n
      unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
        throwError "A1-c2：標準三公理以外への依存 {n}: {axioms}、経路 {path.reverse}"
    | _ => pure ()
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    checkUnconditional (deps.toList.map (fun d => (d, n :: path)) ++ rest) seen

run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.VarpiComparison]
  let mut seen : Array Name := #[]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless modules.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "A1-c2：標準三公理以外への依存 {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  unless seen.size == modules.size do throwError "A1-c2：対象モジュールの監査漏れ"
  -- 局所記法の構文実装は公理検査に含め、論理的な依存探索は公開宣言を起点とする。
  let roots : List Name := [
    ``perfectPrismPDTensorVarpiDividedPowers_of_unconditional,
    ``perfectPrismPDTensorVarpiDividedPowers_generator_of_unconditional,
    ``perfectPrismPDTensorVarpi_isDPMorphism_of_unconditional,
    ``hodgeTate_completelyFaithfullyFlat_iff_of_unconditional,
    ``hodgeTate_coefficient_comparison_of_unconditional]
  let deps ← liftCoreM <| checkUnconditional (roots.map (fun n => (n, []))) {}
  logInfo m!"A1-c2：生成宣言を含む {count} 宣言、標準三公理のみ。"
  logInfo m!"A1-c2：型と値の依存 {deps.size} 宣言、旧 hpR 宣言への依存なし。"
end
