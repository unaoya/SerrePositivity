import SerrePositivity.KST.DerivedGeometry
import Lean.Util.CollectAxioms

/-!
概要：K-L4 の全公開宣言の推移的な公理依存を監査する。
方針：名前空間内の宣言を列挙し collectAxioms で検証する。
規約：propext・Classical.choice・Quot.sound のみを許す。
使われ方：KST D4、Bondal–van den Bergh Thm 3.1.1、Neeman 1992 Thm 2.1、
TT 3.19・8.1、Toën §3.2 の保存単位ごとの受入検証。
-/

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let required : Array Name := #[
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.forget,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.underlyingCohomology,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.hasQuasicoherentCohomology,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.dqcInclusion]
  for name in required do
    unless env.contains name do throwError "Missing K-L4 declaration: {name}"
  for mod in env.header.modules do
    if (`SerrePositivity.KTheory).isPrefixOf mod.module then
      throwError "K-L4 must not depend on K-theory: {mod.module}"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    unless (`SerrePositivity.KST.DerivedGeometry).isPrefixOf name do continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax =>
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains ax)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"
    count := count + 1
  if count == 0 then throwError "No K-L4 declarations audited"
  logInfo m!"K-L4 audit: {count} declarations; standard axioms only; no KTheory imports."
