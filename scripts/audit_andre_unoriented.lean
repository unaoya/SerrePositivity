import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Initiality
import Mathlib.Util.AssertNoSorry

/-!
# 向きなし André 入力圏と源の監査

## 概要
BS Rem 7.15（著者版 p.62）の向きなし入力圏・同値・源の公開宣言を監査する。

## 方針
公開18宣言の assert_no_sorry と実装全宣言の推移的な公理検査を行う。

## 規約
許可する公理は propext・Classical.choice・Quot.sound の三つ。

## 使われ方
lake env lean scripts/audit_andre_unoriented.lean で実行する。
-/

assert_no_sorry SerrePositivity.BhattScholze.Andre.BoundedPrismInputUnoriented
 SerrePositivity.BhattScholze.Andre.BoundedPrismInputUnoriented.orient
 SerrePositivity.BhattScholze.Andre.BoundedPrismInputUnoriented.orient_generator
 SerrePositivity.BhattScholze.Andre.BoundedPrismInputUnoriented.orient_ideal
 SerrePositivity.BhattScholze.Andre.BoundedPrismInputUnoriented.category
 SerrePositivity.BhattScholze.Andre.BoundedPrismInputUnoriented.orientFunctor
 SerrePositivity.BhattScholze.Andre.BoundedPrismInputUnoriented.forget
 SerrePositivity.BhattScholze.Andre.BoundedPrismInputUnoriented.orientationIso
 SerrePositivity.BhattScholze.Andre.BoundedPrismInputUnoriented.forgetFunctor
 SerrePositivity.BhattScholze.Andre.BoundedPrismInputUnoriented.forgetFunctor_map_toRingHom
 SerrePositivity.BhattScholze.Andre.BoundedPrismInputUnoriented.equivalence
 SerrePositivity.BhattScholze.Andre.BoundedPrismInput.initial_unoriented
 SerrePositivity.BhattScholze.Andre.powerRootPrismMonicSourceInput_initial_unoriented

 SerrePositivity.BhattScholze.Andre.powerRootPrismMonicSourceInputObjectOfMonicPositive_unoriented
 SerrePositivity.BhattScholze.Andre.powerRootPrismMonicSourceInput_isInitialOfMonicPositive_unoriented
 SerrePositivity.BhattScholze.Andre.powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_unoriented
 SerrePositivity.BhattScholze.Andre.powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_base_coeff_unoriented

 SerrePositivity.BhattScholze.Andre.existsUnique_powerRootPrismMonicPrismHom_of_absolute_input_unoriented

#check SerrePositivity.BhattScholze.Andre.powerRootPrismMonicSourceInputObjectOfMonicPositive_unoriented

#check SerrePositivity.BhattScholze.Andre.powerRootPrismMonicSourceInput_isInitialOfMonicPositive_unoriented

#check SerrePositivity.BhattScholze.Andre.powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_unoriented

#check SerrePositivity.BhattScholze.Andre.powerRootPrismMonicSourceEnvelopeRingEquivOfMonicPositive_base_coeff_unoriented

#check SerrePositivity.BhattScholze.Andre.existsUnique_powerRootPrismMonicPrismHom_of_absolute_input_unoriented

open Lean in
run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.InputCategory,
    `SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Initiality]
  let mut seen : Array Name := #[]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  unless seen.size == expected.size do
    throwError "Missing André unoriented modules"
  logInfo m!"André unoriented audit passed: {count} declarations, standard axioms only."
