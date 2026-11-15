import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Residue
import Mathlib.Util.AssertNoSorry

/-!
# A1-d の独立した実行用監査

## 概要
BS Rem 7.15（著者版 p.62）の初期係数商・raw 残余商・実還元 H⁰ の公開宣言を監査する。

## 方針
受渡しの型全体を固定して適用を検査し、全公開宣言の sorry 非依存性と、
補助生成宣言を含む二つの実装モジュールの推移的公理を調べる。

## 規約
許可する公理は propext・Classical.choice・Quot.sound のみ。

## 使われ方
`lake env lean scripts/audit_andre_initial_coefficient.lean` で独立に実行する。
-/

open SerrePositivity SerrePositivity.BhattScholze SerrePositivity.BhattScholze.Andre
open SerrePositivity.BhattScholze.Andre.InitialCoefficient CategoryTheory
attribute [local instance] HasDerivedCategory.standard
noncomputable section
universe u
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]

assert_no_sorry initialCoefficientIdeal_eq
assert_no_sorry initialCoefficientPrincipalEquiv
assert_no_sorry initialCoefficientPrincipalEquiv_mk
assert_no_sorry initialCoefficientEquiv
assert_no_sorry initialCoefficientEquiv_coeff
assert_no_sorry initialCoefficientBaseMap
assert_no_sorry initialCoefficientBaseMap_mk
assert_no_sorry initialCoefficientAlgebra
assert_no_sorry initialCoefficientAlgEquiv
assert_no_sorry initialCoefficient_free
assert_no_sorry initialCoefficient_faithfullyFlat
assert_no_sorry freeDelta_prime_regular
assert_no_sorry rawResidueBaseMap
assert_no_sorry rawResidueBaseMap_mk
assert_no_sorry rawResidueBaseMap_eq_source
assert_no_sorry rawResidueAlgebra
assert_no_sorry rawResidueBase_faithfullyFlat
assert_no_sorry rawResidueRestrictionLinearEquiv
assert_no_sorry rawResidue_faithfullyFlat
assert_no_sorry sourceResidueH0_faithfullyFlat

-- 受渡しで指定された型全体を検査し、追加仮定がないことを固定する。
example (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
  let hp := Nat.Prime.pos (Fact.out : p.Prime)
  let P := _root_.SerrePositivity.BhattScholze.Semiperfectoid.PowerRootPolynomial A p hp
  let E := _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
  let dP := algebraMap A P W.generator
  let a := powerRootPrismMonicUnaryFamily (p := p) f
  let L₀ := PowerRootUnaryFreeDeltaRing A p hp
  let Q := L₀ ⧸ Ideal.span {(p : L₀), MvPolynomial.C dP}
  let R := A ⧸ Ideal.span {(p : A), W.generator}
  let Res := DeltaAdjoinDivisionResidue E dP a
  let κ := powerRootSourceQuotientCoefficientMap_of_unconditional W
  letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  letI : Module Q Res := Algebra.toModule
  Module.FaithfullyFlat R ((ModuleCat.restrictScalars κ).obj (ModuleCat.of Q Res)) :=
  rawResidue_faithfullyFlat W hW f hf hdeg

-- 受渡しで指定された型全体を検査し、追加仮定がないことを固定する。
example (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
  let R := A ⧸ Ideal.span {(p : A), W.generator}
  Module.FaithfullyFlat R
    ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
        (Ideal.span {(p : A), W.generator}))).obj
        (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f)).obj) :=
  sourceResidueH0_faithfullyFlat W hW f hf hdeg

#print axioms rawResidue_faithfullyFlat
#print axioms sourceResidueH0_faithfullyFlat

open Lean in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Residue]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless modules.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "A1-d: 標準三公理以外への依存 {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  unless seen.size == modules.size do throwError "A1-d: 対象モジュールの監査漏れ"
  logInfo m!"A1-d: 公開20宣言はsorry非依存、生成宣言を含む {count} 宣言は標準三公理のみ。"
