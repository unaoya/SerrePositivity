module

import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Initiality
import Mathlib.Util.AssertNoSorry

/-!
# A1-f：向きなし入力圏の専用監査

## 概要
向きなし対象・圏同値・初期性の公開宣言とモジュール全宣言を検査する。
BS 著者版 Remark 7.15 の包を扱う、向きなし入力圏の宣言を監査する。

## 方針
assert_no_sorry と推移的な公理の列挙を併用する。
## 規約
許可公理は propext・Classical.choice・Quot.sound の三つだけ。
## 使われ方
lake env lean SerrePositivity/BhattScholze/Andre/PowerRootEnvelope/Audit/Unoriented.lean で実行する。
-/

open SerrePositivity.BhattScholze SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits

assert_no_sorry BoundedPrismInputUnoriented
assert_no_sorry BoundedPrismInputUnoriented.orient
assert_no_sorry BoundedPrismInputUnoriented.orient_generator
assert_no_sorry BoundedPrismInputUnoriented.orient_ideal
assert_no_sorry BoundedPrismInputUnoriented.category
assert_no_sorry BoundedPrismInputUnoriented.orientFunctor
assert_no_sorry BoundedPrismInputUnoriented.forget
assert_no_sorry BoundedPrismInputUnoriented.orientationIso
assert_no_sorry BoundedPrismInputUnoriented.forgetFunctor
assert_no_sorry BoundedPrismInputUnoriented.forgetFunctor_map_toRingHom
assert_no_sorry BoundedPrismInputUnoriented.equivalence
assert_no_sorry BoundedPrismInput.initial_unoriented
assert_no_sorry powerRootPrismMonicSourceInput_initial_unoriented

noncomputable section
universe u
variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A] [CommRing S]

-- 公開型を固定し、基底以外の完全性や生成元データを要求しないことを確認する。
example (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (c : A ⧸ W.ideal →+* S) :
    BoundedPrismInput W c ≌ BoundedPrismInputUnoriented W c :=
  BoundedPrismInputUnoriented.equivalence

example (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    IsInitial (BoundedPrismInputUnoriented.forget
      (powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg)) :=
  powerRootPrismMonicSourceInput_initial_unoriented W hW f hf hdeg

#check BoundedPrismInputUnoriented.equivalence
#check powerRootPrismMonicSourceInput_initial_unoriented
#print axioms BoundedPrismInputUnoriented.equivalence
#print axioms powerRootPrismMonicSourceInput_initial_unoriented

open Lean in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.InputCategory,
    `SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Initiality]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless modules.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "A1-f: 標準三公理以外への依存 {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  unless seen.size == modules.size do throwError "A1-f: 対象モジュールの監査漏れ"
  logInfo m!"A1-f: 公開13宣言はsorry非依存、生成宣言を含む {count} 宣言は標準三公理のみ。"
