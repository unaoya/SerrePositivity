module

import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.VarpiComparison
import Mathlib.Util.AssertNoSorry

/-!
## 概要
根の包絡における係数と生成元の変更、平坦性の比較に関する宣言を監査する。

## 方針
公開定理のsorry不在を検査し、対象モジュールの生成宣言まで公理依存を照会する。

## 規約
BS著者版Remark 7.15。許す公理はpropext・Classical.choice・Quot.soundの三つとする。

## 使われ方
ライブラリへimportせず、生成元の比較の独立した監査として実行する。
-/

open SerrePositivity.BhattScholze.Andre.VarpiComparison

assert_no_sorry span_power_eq_of_unit
assert_no_sorry completelyFlat_of_le
assert_no_sorry completelyFlat_iff
assert_no_sorry residueTensor_faithfullyFlat
assert_no_sorry completelyFaithfullyFlat_iff
assert_no_sorry completelyFlat_iff_flat_reduction
assert_no_sorry completelyFaithfullyFlat_iff_faithfullyFlat_reduction
assert_no_sorry algebraQuotient_faithfullyFlat
assert_no_sorry powerRootPDTensorQuotientEquiv
assert_no_sorry powerRootPDTensorQuotientEquiv_generator
assert_no_sorry primeVarpiDoubleQuotientEquiv
assert_no_sorry varpiCoefficientAlgebra
assert_no_sorry varpiCoefficientAlgEquiv
assert_no_sorry perfectPrismPDTensorVarpiEquiv
assert_no_sorry perfectPrismPDTensorVarpiEquiv_one_tmul
assert_no_sorry perfectPrismPDTensorVarpiEquiv_generator
assert_no_sorry perfectPrismPDTensorVarpiDividedPowers
assert_no_sorry perfectPrismPDTensorVarpiDividedPowers_generator
assert_no_sorry perfectPrismPDTensorVarpi_isDPMorphism
assert_no_sorry hodgeTateVarpiPDAlgEquiv
assert_no_sorry hodgeTateVarpiPowerQuotientAlgebra
assert_no_sorry hodgeTateVarpi_free_over_powerQuotient
assert_no_sorry hodgeTate_completelyFaithfullyFlat_iff
assert_no_sorry hodgeTate_coefficient_comparison

assert_no_sorry rootCoefficientChange_baseMap
assert_no_sorry quotientCoefficientAlgebra
assert_no_sorry quotientCoefficientAlgEquiv
assert_no_sorry powerRootPDTensorChangeEquiv
assert_no_sorry primePDTensorVarpiEquiv

#print axioms completelyFlat_iff_flat_reduction
#print axioms completelyFaithfullyFlat_iff_faithfullyFlat_reduction
#print axioms algebraQuotient_faithfullyFlat
#print axioms perfectPrismPDTensorVarpi_isDPMorphism
#print axioms hodgeTate_coefficient_comparison

#print axioms primePDTensorVarpiEquiv

meta section
open Lean Elab Command
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
      throwError "A1-c：標準三公理以外への依存 {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  unless seen.size == modules.size do
    throwError "A1-c：対象モジュールの監査漏れ"
  logInfo m!"A1-c：生成宣言を含む {count} 宣言、標準三公理のみ。"
end
