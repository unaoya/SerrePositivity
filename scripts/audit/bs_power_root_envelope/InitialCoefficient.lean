module

import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Residue
import Mathlib.Util.AssertNoSorry

/-!
## 概要
根の包絡の初期係数に関する公開宣言と、忠実平坦性の受け渡し型・公理依存を検査する。

## 方針
係数制限と導来還元H⁰の結論型を明示して既存の定理を適用し、生成宣言を含む依存を列挙する。

## 規約
BS著者版Remark 7.15。許す公理はpropext・Classical.choice・Quot.soundの三つとし、監査用定義は非公開に保つ。

## 使われ方
ライブラリへimportせず、根の包絡の独立した監査として実行する。
-/

-- 専用監査だけのモジュールなので、受渡し型の検査用定義は非公開のまま保持する。
set_option linter.privateModule false

open SerrePositivity SerrePositivity.BhattScholze SerrePositivity.BhattScholze.Andre
open SerrePositivity.BhattScholze.Andre.InitialCoefficient CategoryTheory
attribute [local instance] HasDerivedCategory.standard
noncomputable section
universe u
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]

/-- A1-b の指定した自然な係数制限作用のままの結論型。追加仮定なしの適用を検査する。 -/
private def A1dRawTarget (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) : Prop :=
  let hp := Nat.Prime.pos (Fact.out : p.Prime)
  let P := PowerRootPolynomial A p hp
  let E := powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
  let dP := algebraMap A P W.generator
  let a := powerRootPrismMonicUnaryFamily (p := p) f
  let L₀ := PowerRootUnaryFreeDeltaRing A p hp
  let Q := L₀ ⧸ Ideal.span {(p : L₀), MvPolynomial.C dP}
  let R := A ⧸ Ideal.span {(p : A), W.generator}
  let Res := DeltaAdjoinDivisionResidue E dP a
  let κ := powerRootSourceQuotientCoefficientMap_of_unconditional W
  letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  letI : Module Q Res := Algebra.toModule
  Module.FaithfullyFlat R ((ModuleCat.restrictScalars κ).obj (ModuleCat.of Q Res))

/-- A1-b の実導来還元 H⁰ の結論型。既存 H⁰ 同型に沿う正確な受渡しを検査する。 -/
private def A1dH0Target (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) : Prop :=
  let R := A ⧸ Ideal.span {(p : A), W.generator}
  Module.FaithfullyFlat R
    ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
        (Ideal.span {(p : A), W.generator}))).obj
        (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f)).obj)

-- A1-b の受渡しそのものに、追加仮定なしで適用できることを検査する。
example (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) : A1dRawTarget W hW f :=
  rawResidue_faithfullyFlat W hW f hf hdeg

example (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) : A1dH0Target W hW f :=
  sourceResidueH0_faithfullyFlat W hW f hf hdeg

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

#print axioms initialCoefficient_faithfullyFlat

#print axioms rawResidueBaseMap_eq_source

#print axioms rawResidue_faithfullyFlat

#print axioms sourceResidueH0_faithfullyFlat

meta section
open Lean Elab Command
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
      throwError "A1-d：標準三公理以外への依存 {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  unless seen.size == modules.size do throwError "A1-d：対象モジュールの監査漏れ"
  logInfo m!"A1-d：生成宣言を含む {count} 宣言、標準三公理のみ。"
end
