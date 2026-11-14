module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootPolynomial
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Varpi
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PrincipalDP
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.DividedPowerPrime
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Completion
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.BhattScholze.Prism.Bounded.Tilt

/-!
# 方程式商・入力射と mod p の pd 包

## 概要
係数 Frobenius と指数 Frobenius の分離、無限根多項式環の普遍性、方程式商 S とその p 完備化の普遍性、原典の順序による完備入力環、rank 1 の互換根列による δ 射、試験 prism の剰余根列からの入力 δ 射、mod p 分冪包、Frobenius 二元商と ϖ 係数、モニック分冪表示環の自由性と係数還元。
BS 著者版 Remark 7.15 の方程式商を定め、入力射と mod p の分冪包を比較する。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/CompletionPD`、`PowerRootEnvelope/CompletionPrism`、`PowerRootEnvelope/InputUniversal`、`PowerRootEnvelope/Unconditional/Localization`、`PowerRootEnvelope/Unconditional/Residue`、`PowerRootEnvelope/VarpiPD`、`Variants/Auxiliary`、`Variants/MonicRootedExtension`。
-/

universe u v

/-! ## 無限 p 冪根環上のモニック入力の実 mod p 分冪包

## 概要

p 正則・p 局所 δ 環上の無限根多項式環で、モニック入力の mod p 一次関係商に
実分冪構造と pd 普遍性を与える。完全 prism からこれらの前提を供給する。
BS 著者版 Remark 7.15(1)（著者版 p.62）の無限根変数を含む実 pd 計算。

## 方針

無限根環の実 δ 構造、自由性による p 正則性、実係数商比較によるモニック入力の
mod p 正則性を既存の正則一元分冪包の構成へ渡す。

## 規約

台環は同じ無限根環の実 mod p 商上の一次関係商。
R/ϖ 係数および prismatic Frobenius 引戻しとの同定はこのファイルだけでは主張しない。

## 使われ方

原典のモニック根拡大の実 pd 包の表示を、prismatic envelope の剰余比較へ接続する。
-/

@[expose] public noncomputable section PowerRootMonicModPrimePDEnvelope

set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "Q" => P ⧸ Ideal.span {(p : P)}
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : P)})
/-- 概要：無限根環の通常変数 Y₀ で多項式 f を評価した入力元。
方針：既存の標準評価射を名前付きの元として固定する。
規約：分冪構造の型照合で評価の内部を展開し続けないよう irreducible とする。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の無限根環の一元入力。 -/
@[irreducible] def powerRootMonicPDInput (f : Polynomial A) : P :=
  powerRootPolynomialBaseMap A p hp f

local notation "root" f => powerRootMonicPDInput p f

/-- 概要：名前付きモニック入力は実 mod p 商で非零因子。
方針：入力元の定義を一度だけ展開し、係数商比較で得た正則性を使う。
規約：表示の内部展開を他の分冪構造の型へ持ち込まない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の無限根 pd 包の正則入力。 -/
theorem powerRootMonicPDInput_modPrime_regular (f : Polynomial A) (hf : f.Monic) :
    IsSMulRegular Q (bar (root f)) := by
  simpa only [powerRootMonicPDInput] using
    powerRootPolynomial_monic_mod_prime_regular A p hp f hf

/-- 概要：p 局所な係数環上の無限根多項式環も p 局所。
方針：係数の単元を標準係数射で送る。
規約：係数環の p 完備性はこの段階では不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の階乗計算の入力。 -/
theorem powerRootPolynomial_primeLocal
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) :
    ∀ m : ℕ, ¬p ∣ m → IsUnit (m : P) := by
  intro m hm
  simpa only [map_natCast] using (hlocal m hm).map (algebraMap A P)

/-- 概要：無限根環上のモニック入力の実 mod p 分冪表示環の台環。
方針：通常変数 Y₀ での評価を実 mod p 商へ送って一次関係を課す。
規約：台環の定義そのものにはモニック性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の無限根環上の pd 包。 -/
abbrev PowerRootMonicModPrimePDEnvelope (f : Polynomial A) :=
  PrincipalDPPresentation Q (bar (root f))

/-- 概要：無限根環上のモニック入力の mod p 表示環には実分冪構造がある。
方針：無限根環の δ 持ち上げと p 正則性、入力の mod p 正則性を内部で供給する。
規約：係数環の p 正則性・p 局所性・δ 構造は明示する。f の正次数は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の無限根環上の実 pd 包の構造。 -/
def powerRootMonicModPrimeDividedPowers
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (f : Polynomial A) (hf : f.Monic) :
    DividedPowers (principalDPPositiveIdeal (bar (root f))) :=
  regularPrincipalModPrimeDividedPowers (A := P) (p := p) (powerRootPolynomial_primeLocal p hlocal)
    (powerRootPolynomial_primeRegular p hpA) (powerRootPolynomialDelta p hpA D) (root f)
    (powerRootMonicPDInput_modPrime_regular p f hf)

/-- 概要：無限根環上の入力元の n 次分冪は標準の n 次生成元。
方針：正則一元構成の生成元公式へ無限根環の実入力を代入する。
規約：全ての次数 n を含む。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の普遍性と明示表示の比較。 -/
theorem powerRootMonicModPrimeDividedPowers_base_apply
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (f : Polynomial A) (hf : f.Monic) (n : ℕ) :
    (powerRootMonicModPrimeDividedPowers p hlocal hpA D f hf).dpow n
      (algebraMap Q (PowerRootMonicModPrimePDEnvelope p f) (bar (root f))) =
      principalDPGenerator (bar (root f)) n := by
  unfold powerRootMonicModPrimeDividedPowers
  with_reducible exact
    (@regularPrincipalModPrimeDividedPowers_base_apply p inferInstance P inferInstance
      (powerRootPolynomial_primeLocal p hlocal)
      (powerRootPolynomial_primeRegular p hpA) (powerRootPolynomialDelta p hpA D) (root f)
      (powerRootMonicPDInput_modPrime_regular p f hf) n)

/-- 概要：無限根環上のモニック入力の実 mod p 分冪包から分冪標的への射は一意に存在。
方針：構成した実構造と標準生成元の公式を一次関係商の普遍性へ渡す。
規約：標的の p ねじれ・正則性・δ 構造・完備性を要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の無限根環上の実 pd 包の普遍性。 -/
theorem existsUnique_powerRootMonicModPrimePDMorphism
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (f : Polynomial A) (hf : f.Monic)
    {T : Type v} [CommRing T] [Algebra Q T] {I : Ideal T} (Ht : DividedPowers I)
    (hyT : algebraMap Q T (bar (root f)) ∈ I) :
    ∃! F : PowerRootMonicModPrimePDEnvelope p f →ₐ[Q] T,
      (powerRootMonicModPrimeDividedPowers p hlocal hpA D f hf).IsDPMorphism Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism _
    (powerRootMonicModPrimeDividedPowers p hlocal hpA D f hf)
    (powerRootMonicModPrimeDividedPowers_base_apply p hlocal hpA D f hf) Ht hyT

/-- 概要：完全 prism 上の無限根環で、モニック入力の実 mod p 分冪構造を構成する。
方針：完全性から係数環の p 正則性と p 局所性を供給する。
規約：追加の正則性や分冪構造の存在を前提に残さない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の完全 prism 上の無限根 pd 包。 -/
def perfectPrismPowerRootMonicModPrimeDividedPowers
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) :
    DividedPowers (principalDPPositiveIdeal (bar (root f))) :=
  powerRootMonicModPrimeDividedPowers p (perfectPrism_primeLocal W hW) hW.p_mul_injective
    W.deltaStructure f hf

/-- 概要：完全 prism 上の無限根環のモニック入力について実 pd 普遍射は一意に存在。
方針：完全 prism から係数の全補助条件を供給した構成を適用する。
規約：モニック多項式の正次数も標的の正則性も要求しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の無限根 pd 包の具体的な普遍性。 -/
theorem existsUnique_perfectPrismPowerRootMonicModPrimePDMorphism
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic)
    {T : Type v} [CommRing T] [Algebra Q T] {I : Ideal T} (Ht : DividedPowers I)
    (hyT : algebraMap Q T (bar (root f)) ∈ I) :
    ∃! F : PowerRootMonicModPrimePDEnvelope p f →ₐ[Q] T,
      (perfectPrismPowerRootMonicModPrimeDividedPowers p W hW f hf).IsDPMorphism Ht F.toRingHom :=
  existsUnique_powerRootMonicModPrimePDMorphism p (perfectPrism_primeLocal W hW) hW.p_mul_injective
    W.deltaStructure f hf Ht hyT


/-- 概要：無限根環の実 mod p 商では p は零。
方針：定義の p 主イデアルへの所属を使う。
規約：元の係数環の標数は任意。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の明示切断表示への入力。 -/
theorem powerRootModPrime_prime_eq_zero : (p : Q) = 0 := by
  change bar (p : P) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- 概要：無限根環上の実 mod p 分冪包の台環は入力の p 乗商上の可算切断表示。
方針：一次関係商の明示的な係数商上の代数同型を同じ実台環へ適用する。
規約：台環の同型自体にはモニック性や prism は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の無限根 pd 包の具体的な自由表示。 -/
def powerRootMonicModPrimePDEnvelope_truncatedEquiv (f : Polynomial A) :
    letI := principalDPQuotientAlgebra hp (powerRootModPrime_prime_eq_zero (A := A) p)
      (bar (root f))
    PowerRootMonicModPrimePDEnvelope p f ≃ₐ[Q ⧸ Ideal.span {(bar (root f)) ^ p}]
      PrincipalDPTruncatedPresentation p (bar (root f)) :=
  principalDPTruncatedQuotientAlgEquiv p (powerRootModPrime_prime_eq_zero p) _

/-- 概要：無限根環上の実 mod p 分冪包の台環は入力の p 乗係数商上自由。
方針：同じ既存係数商作用に明示切断表示を介した自由性を適用する。
規約：分冪構造の構成に必要なモニック性は、台加群の自由性には不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の無限根 pd 包の自由性。 -/
theorem powerRootMonicModPrimePDEnvelope_quotient_free (f : Polynomial A) :
    letI := principalDPQuotientAlgebra hp (powerRootModPrime_prime_eq_zero (A := A) p)
      (bar (root f))
    Module.Free (Q ⧸ Ideal.span {(bar (root f)) ^ p}) (PowerRootMonicModPrimePDEnvelope p f) :=
  principalDPPresentation_free_via_truncated p (powerRootModPrime_prime_eq_zero p) _

end SerrePositivity.BhattScholze.Andre

end PowerRootMonicModPrimePDEnvelope

/-! ## 無限 p 冪根多項式環上のモニック分冪表示環の自由性

## 概要

標数 p の係数環上の無限 p 冪根多項式環 P 内で、モニック f の像の分冪表示環は
元の係数環上自由であり、f が正次数なら忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の通常代数の自由性計算。

## 方針

同じ実 fᵖ 商の自由性・忠実平坦性と、その商上の分冪表示環の自由性を合成する。
標準多項式係数射で拡張したイデアルを、f の像の p 乗の主イデアルへ同定する。

## 規約

対象は既存の PrincipalDPPresentation である。
実 prismatic envelope の Frobenius 引戻しや実 pd 包との同定をこのファイルだけでは主張しない。

## 使われ方

原典の具体的 pd 計算と既存候補の比較を補完する際に、通常係数環の自由性を供給する。
-/

@[expose] public noncomputable section PowerRootMonicPDFlat

namespace SerrePositivity.BhattScholze.Andre
open Polynomial
variable (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p)
local notation "P" => PowerRootPolynomial R p hp

/-- 概要：無限 p 冪根変数内のモニック関係の分冪表示環は元の係数環上自由。
方針：実 fᵖ 商の自由性と、その商上の分冪表示環の自由性をスカラー塔で合成する。
規約：p は素数で係数環内で零とする。自由性には f の正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 表示の自由性。 -/
theorem powerRootMonicDPPresentation_free (hprime : p.Prime) (hpR : (p : R) = 0)
    (f : R[X]) (hf : f.Monic) :
    Module.Free R (PrincipalDPPresentation P (powerRootPolynomialBaseMap R p hp f)) := by
  let := powerRootPolynomialBaseAlgebra R p hp
  let y := powerRootPolynomialBaseMap R p hp f
  have hpP : (p : P) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap R P) hpR
  have heI : (Ideal.span {f ^ p}).map (algebraMap R[X] P) = Ideal.span {y ^ p} := by
    rw [powerRootPolynomialQuotient_ideal, map_pow]
  have hQ : Module.Free R (P ⧸ Ideal.span {y ^ p}) := by
    have h := powerRootPolynomialPowerQuotient_free R p hp f hf
    change Module.Free R (P ⧸ (Ideal.span {f ^ p}).map (algebraMap R[X] P)) at h
    rw [heI] at h
    exact h
  let := principalDPQuotientAlgebra hprime.pos hpP y
  let := principalDPQuotient_isScalarTower_base (A := R) hprime.pos hpP y
  let := principalDPPresentation_quotient_free p hprime hpP y
  let := hQ
  exact Module.Free.trans (R := R) (S := P ⧸ Ideal.span {y ^ p})
    (M := PrincipalDPPresentation P y)

/-- 概要：正次数モニック関係の分冪表示環は元の係数環上忠実平坦。
方針：同じ実 fᵖ 商の忠実平坦性を標準係数射のスカラー塔で表示環へ移す。
規約：係数環の非零性や被約性は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の原典の通常平坦性計算。 -/
theorem powerRootMonicDPPresentation_faithfullyFlat (hprime : p.Prime) (hpR : (p : R) = 0)
    (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat R
      (PrincipalDPPresentation P (powerRootPolynomialBaseMap R p hp f)) := by
  let := powerRootPolynomialBaseAlgebra R p hp
  let y := powerRootPolynomialBaseMap R p hp f
  have hpP : (p : P) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap R P) hpR
  have heI : (Ideal.span {f ^ p}).map (algebraMap R[X] P) = Ideal.span {y ^ p} := by
    rw [powerRootPolynomialQuotient_ideal, map_pow]
  apply principalDPPresentation_faithfullyFlat_of_quotient p hprime hpP y
  have h := powerRootPolynomialPowerQuotient_faithfullyFlat R p hp f hf hdeg
  change Module.FaithfullyFlat R (P ⧸ (Ideal.span {f ^ p}).map (algebraMap R[X] P)) at h
  rw [heI] at h
  exact h

end SerrePositivity.BhattScholze.Andre

end PowerRootMonicPDFlat

/-! ## 係数 mod p 無限根環上の実分冪包

## 概要

完全 prism の係数環 A の mod p 無限根環 (A/(p))[Y¹⸍ᵖ∞] 上で、
モニック入力の実分冪構造と普遍性を構成する。同じ台環は A/(p) 上自由で、
正次数入力では忠実平坦。BS 著者版 Remark 7.15(1)（著者版 p.62）の係数環上の自由性の計算。

## 方針

無限根環の実 mod p 商との係数比較同型と一次関係商の移送を合成する。
同じ台環の通常の自由性・忠実平坦性には既存のモニック冪商の基底計算を使う。

## 規約

元のモニック多項式は A 上に持ち上げて与える。R/ϖ 係数への比較と
prismatic Frobenius 引戻しの同定をこのファイルだけでは主張しない。

## 使われ方

実 pd 包の構造・普遍性と通常の自由性・忠実平坦性を同じ係数環・台環へ集約する。
-/

@[expose] public noncomputable section PowerRootCoefficientPDEnvelope

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "Q" => P ⧸ Ideal.span {(p : P)}
local notation "q" => Ideal.Quotient.mk (Ideal.span {(p : P)})
local notation "R" => A ⧸ Ideal.span {(p : A)}
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "N" => PowerRootPolynomial R p hp
local notation "e" => powerRootPolynomialModPrimeEquiv A p hp
local notation "y" f => q (powerRootMonicPDInput p f)

/-- 概要：係数 mod p 無限根環におけるモニック多項式の指定入力元。
方針：係数を mod p に写した多項式を Y₀ で評価する。
規約：分冪構造の型照合で内部評価を展開し続けないよう irreducible とする。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数商上の実 pd 包の入力。 -/
@[irreducible] def powerRootCoefficientPDInput (f : Polynomial A) : N :=
  powerRootPolynomialBaseMap R p hp (f.map bar)

local notation "z" f => powerRootCoefficientPDInput p f

/-- 概要：実 mod p 比較同型は元の入力を係数商上の指定入力へ送る。
方針：入力元の定義を明示展開し、商同型と評価の自然性を使う。
規約：この比較自体にはモニック性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の分冪包の係数比較。 -/
theorem powerRootCoefficientPDInput_compare (f : Polynomial A) : e (y f) = z f := by
  unfold powerRootMonicPDInput powerRootCoefficientPDInput
  rw [powerRootPolynomialModPrimeEquiv_mk, powerRootPolynomialModPrimeMap_baseMap]

/-- 概要：係数商上の無限根環の一次関係商の実台環。
方針：同じ係数商上の指定入力に γ₁=z の関係を課す。
規約：分冪構造の存在は別途構成する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の pd 包の自由性と構造の共通台環。 -/
abbrev PowerRootCoefficientPDEnvelope (f : Polynomial A) := PrincipalDPPresentation N (z f)

/-- 概要：実 mod p 無限根 pd 表示と係数商上の無限根 pd 表示は環同型。
方針：係数比較が入力を保つことを一次関係商の係数同型へ渡す。
規約：標準係数と全標準生成元を保つ同型を使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 構造の移送。 -/
def powerRootCoefficientPDEnvelopeEquiv (f : Polynomial A) :
    PowerRootMonicModPrimePDEnvelope p f ≃+* PowerRootCoefficientPDEnvelope p f :=
  principalDPRingEquivOfEq e (y f) (z f) (powerRootCoefficientPDInput_compare p f)

/-- 概要：係数商上の無限根環の正次数イデアルに実分冪構造を与える。
方針：完全 prism 上で構成した実 mod p 構造を係数比較同型で移す。
規約：追加の分冪構造・正則性を仮定として残さない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数 mod p 無限根 pd 包。 -/
def powerRootCoefficientDividedPowers
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) : DividedPowers (principalDPPositiveIdeal (z f)) :=
  principalDPTransportDividedPowers e (y f) (z f) (powerRootCoefficientPDInput_compare p f)
    (perfectPrismPowerRootMonicModPrimeDividedPowers p W hW f hf)

/-- 概要：移送した実構造で入力元の n 次分冪は n 次標準生成元。
方針：係数同型の構造移送の公式と移送前の標準値を使う。
規約：名前付き入力を保ち、型照合では評価の内部を展開しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 普遍性への標準値。 -/
theorem powerRootCoefficientDividedPowers_base_apply
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (n : ℕ) :
    (powerRootCoefficientDividedPowers p W hW f hf).dpow n
      (algebraMap N (PowerRootCoefficientPDEnvelope p f) (z f)) = principalDPGenerator (z f) n := by
  have hsγ : ∀ k, (perfectPrismPowerRootMonicModPrimeDividedPowers p W hW f hf).dpow k
      (algebraMap Q (PowerRootMonicModPrimePDEnvelope p f) (y f)) =
        principalDPGenerator (y f) k := by
    intro k
    unfold perfectPrismPowerRootMonicModPrimeDividedPowers
    with_reducible exact
      (@powerRootMonicModPrimeDividedPowers_base_apply A inferInstance p inferInstance
        (perfectPrism_primeLocal W hW) hW.p_mul_injective W.deltaStructure f hf k)
  have h := principalDPTransportDividedPowers_base_apply e (y f) (z f)
    (powerRootCoefficientPDInput_compare p f)
    (perfectPrismPowerRootMonicModPrimeDividedPowers p W hW f hf) hsγ n
  unfold powerRootCoefficientDividedPowers
  with_reducible exact h

/-- 概要：係数商上の無限根環の実 pd 包から任意の分冪標的への射は一意に存在。
方針：移送した構造と標準値の公式を一次関係商の一般普遍性へ渡す。
規約：標的の正則性・ねじれ・δ 構造・完備性には条件を置かない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数商上の実 pd 包の普遍性。 -/
theorem existsUnique_powerRootCoefficientPDMorphism
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic)
    {T : Type v} [CommRing T] [Algebra N T] {I : Ideal T} (Ht : DividedPowers I)
    (hzT : algebraMap N T (z f) ∈ I) :
    ∃! F : PowerRootCoefficientPDEnvelope p f →ₐ[N] T,
      (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism _ (powerRootCoefficientDividedPowers p W hW f hf)
    (powerRootCoefficientDividedPowers_base_apply p W hW f hf) Ht hzT

omit [Fact p.Prime] in
/-- 概要：係数商 A/(p) では p は零。
方針：定義の主イデアルへの所属を使う。
規約：係数環の標数は任意。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の通常自由性の入力。 -/
theorem powerRootCoefficient_prime_eq_zero : (p : R) = 0 := by
  change bar (p : A) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- 概要：同じ実 pd 包の台環は元の係数商 A/(p) 上自由。
方針：モニック性を係数商に移し、無限根モニック冪商の既存の基底計算を使う。
規約：自由性自体に完全 prism や入力の正次数は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の基底環上の実 pd 包の自由性。 -/
theorem powerRootCoefficientPDEnvelope_free (f : Polynomial A) (hf : f.Monic) :
    Module.Free R (PowerRootCoefficientPDEnvelope p f) := by
  unfold PowerRootCoefficientPDEnvelope powerRootCoefficientPDInput
  exact powerRootMonicDPPresentation_free R p hp (Fact.out : p.Prime)
    (powerRootCoefficient_prime_eq_zero p) (f.map bar) (hf.map bar)

/-- 概要：正次数モニック入力の同じ実 pd 包の台環は A/(p) 上忠実平坦。
方針：非零係数商ではモニック次数保存と既存の忠実平坦性を使い、零係数商は自明性で扱う。
規約：正次数は元の f に要求し、係数商の非零性は仮定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の基底環上の忠実平坦性。 -/
theorem powerRootCoefficientPDEnvelope_faithfullyFlat (f : Polynomial A) (hf : f.Monic)
    (hdeg : 0 < f.natDegree) : Module.FaithfullyFlat R (PowerRootCoefficientPDEnvelope p f) := by
  rcases subsingleton_or_nontrivial R with hs | hnR
  · let := hs
    let := powerRootCoefficientPDEnvelope_free p f hf
    rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
    refine ⟨inferInstance, ?_⟩
    intro T _ _ _
    exact Module.subsingleton R T
  · let := hnR
    unfold PowerRootCoefficientPDEnvelope powerRootCoefficientPDInput
    apply powerRootMonicDPPresentation_faithfullyFlat R p hp (Fact.out : p.Prime)
      (powerRootCoefficient_prime_eq_zero p) (f.map bar) (hf.map bar)
    simpa only [hf.natDegree_map bar] using hdeg


/-- 概要：係数商上の無限根環でも p は零。
方針：係数商での等式を標準係数射で送る。
規約：非零性や完全 prism は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の明示切断表示への入力。 -/
theorem powerRootCoefficientRing_prime_eq_zero : (p : N) = 0 := by
  simpa only [map_natCast, map_zero] using
    congrArg (algebraMap R N) (powerRootCoefficient_prime_eq_zero (A := A) p)

/-- 概要：係数商上の実無限根 pd 包は入力の p 乗商上の可算切断表示を持つ。
方針：同じ一次関係商へ既存の明示切断表示同型を適用する。
規約：係数商作用は既存の principalDPQuotientAlgebra を固定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の自然な係数商射の表示。 -/
def powerRootCoefficientPDEnvelope_truncatedEquiv (f : Polynomial A) :
    letI := principalDPQuotientAlgebra hp (powerRootCoefficientRing_prime_eq_zero (A := A) p)
      (z f)
    PowerRootCoefficientPDEnvelope p f ≃ₐ[N ⧸ Ideal.span {(z f) ^ p}]
      PrincipalDPTruncatedPresentation p (z f) :=
  principalDPTruncatedQuotientAlgEquiv p (powerRootCoefficientRing_prime_eq_zero p) _

end SerrePositivity.BhattScholze.Andre

end PowerRootCoefficientPDEnvelope

/-! ## 正則係数元による無限根実分冪包の還元

## 概要

無限根環上のモニック入力の正次数分冪商は係数環上自由。
したがって正則な係数元による商に実分冪構造が降りる。
BS 著者版 Remark 7.15(1)（著者版 p.62）の R/ϖ 係数へ進むための具体的な降下。

## 方針

正次数分冪商を通常のモニック入力商に同定し、既存の無限根モニック商の基底を使う。
係数元の正則性を平坦性で移し、一般の正則元分冪商を適用する。

## 規約

係数環は R=A/(p)。降下する係数元 a の R 内の正則性を明示する。
原典の ϖ との同定はこのファイルだけでは主張しない。

## 使われ方

原典の係数商との比較に際し、補助的なイデアル飽和性を仮定せず実分冪構造を供給する。
-/

@[expose] public noncomputable section PowerRootCoefficientPDRegularReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "R" => A ⧸ Ideal.span {(p : A)}
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "N" => PowerRootPolynomial R p hp
local notation "z" f => powerRootCoefficientPDInput p f
local notation "D" f => PowerRootCoefficientPDEnvelope p f
local notation "J" f => principalDPPositiveIdeal (z f)

/-- 概要：係数商上の無限根環の通常モニック入力商は元の係数商上自由。
方針：名前付き入力を展開し、通常のモニック商の既存の基底を実主イデアル商へ移す。
規約：モニック f の正次数は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の正次数分冪商の自由性の入力。 -/
theorem powerRootCoefficientInputQuotient_free (f : Polynomial A) (hf : f.Monic) :
    Module.Free R (N ⧸ Ideal.span {(z f)}) := by
  unfold powerRootCoefficientPDInput
  let := powerRootPolynomialBaseAlgebra R p hp
  have h := powerRootPolynomialQuotient_free R p hp (f.map bar) (hf.map bar)
  change Module.Free R
    (N ⧸ (Ideal.span {f.map bar}).map (algebraMap (Polynomial R) N)) at h
  rw [powerRootPolynomialQuotient_ideal] at h
  exact h

/-- 概要：実無限根 pd 包を正次数分冪イデアルで割った商は係数商 A/(p) 上自由。
方針：正次数商と通常入力商の代数同型を係数へ制限して自由性を戻す。
規約：完全 prism や実分冪構造の存在自体はこの台加群の自由性には不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数変更時の交わりの制御。 -/
theorem powerRootCoefficientPDPositiveQuotient_free (f : Polynomial A) (hf : f.Monic) :
    Module.Free R ((D f) ⧸ J f) := by
  let := powerRootCoefficientInputQuotient_free p f hf
  exact Module.Free.of_equiv
    ((principalDPPositiveQuotientEquiv (z f)).restrictScalars R).symm.toLinearEquiv

/-- 概要：正則な係数元は正次数分冪商でも正則。
方針：正次数商の係数環上の自由性と平坦性で正則性を移す。
規約：正則性は元の係数商 A/(p) に要求する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数元による実分冪降下。 -/
theorem powerRootCoefficientPDPositiveQuotient_regular (f : Polynomial A) (hf : f.Monic)
    (a : R) (ha : IsSMulRegular R a) :
    IsSMulRegular ((D f) ⧸ J f) (Ideal.Quotient.mk (J f) (algebraMap R (D f) a)) := by
  let := powerRootCoefficientPDPositiveQuotient_free p f hf
  let : Module.Flat R ((D f) ⧸ J f) := Module.Flat.of_free
  exact ha.of_flat (S := (D f) ⧸ J f)

/-- 概要：完全 prism 上の実無限根 pd 包の構造は正則な係数元による実商へ降りる。
方針：係数元の正次数商上の正則性を供給し、一般の正則元分冪商を適用する。
規約：降下後のイデアルは正次数イデアルの実商射による像。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数 R/ϖ へ進む実分冪構造。 -/
def powerRootCoefficientPDRegularReduction
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (a : R) (ha : IsSMulRegular R a) :
    DividedPowers ((J f).map (Ideal.Quotient.mk (Ideal.span {algebraMap R (D f) a}))) :=
  dividedPowersQuotientOfRegular (powerRootCoefficientDividedPowers p W hW f hf)
    (algebraMap R (D f) a) (powerRootCoefficientPDPositiveQuotient_regular p f hf a ha)

/-- 概要：正則係数元による商の入力元の分冪は標準生成元の商像。
方針：商分冪作用の互換性と還元前の標準分冪値の公式を使う。
規約：全次数 n を含む。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数変更後の pd 普遍性への入力。 -/
theorem powerRootCoefficientPDRegularReduction_base_apply
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (a : R) (ha : IsSMulRegular R a) (n : ℕ) :
    (powerRootCoefficientPDRegularReduction p W hW f hf a ha).dpow n
      (Ideal.Quotient.mk _ (algebraMap N (D f) (z f))) =
      Ideal.Quotient.mk _ (principalDPGenerator (z f) n) := by
  unfold powerRootCoefficientPDRegularReduction
  rw [dividedPowersQuotientOfRegular_apply _ _ _ n (principalDPPositiveIdeal_base_mem (z f)),
    powerRootCoefficientDividedPowers_base_apply]


/-- 概要：正則係数元による実還元の標準商射は分冪射。
方針：一般の正則元分冪商の射の互換性を具体的な実構造に適用する。
規約：元の正次数イデアルと還元後の実像を比較する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数変更後の普遍射の照合。 -/
theorem powerRootCoefficientPDRegularReduction_isDPMorphism
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (a : R) (ha : IsSMulRegular R a) :
    (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism
      (powerRootCoefficientPDRegularReduction p W hW f hf a ha)
      (Ideal.Quotient.mk (Ideal.span {algebraMap R (D f) a})) :=
  dividedPowersQuotientOfRegular_isDPMorphism (powerRootCoefficientDividedPowers p W hW f hf)
    (algebraMap R (D f) a) (powerRootCoefficientPDPositiveQuotient_regular p f hf a ha)

end SerrePositivity.BhattScholze.Andre

end PowerRootCoefficientPDRegularReduction

/-! ## Frobenius 二元商の無限根入力と ϖ 係数

## 概要

無限根環 P の (p,d) 商は R/ϖ 上の無限根環と環同型。
係数は逆 Frobenius で移り、根変数の番号は保つ。
BS 著者版 Remark 7.15（著者版 p.62）の入力比較で係数変更を明示する。

## 方針

係数イデアル商との交換と、二元商から ϖ 商への逆係数同型を合成する。

## 規約

入力は係数を逆 Frobenius で移した多項式となる。元の f との同一視は主張しない。

## 使われ方

実完備化の剰余を R/ϖ 上の具体的な主分冪表示に接続する。
-/

@[expose] public noncomputable section PowerRootFrobeniusPairVarpiInput

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => powerRootExponentMonoid p hp
local notation "P" => PowerRootPolynomial A p hp
local notation "dP" => algebraMap A P W.generator
local notation "K" => Ideal.span {(p : A), W.generator}
local notation "KP" => Ideal.span {(p : P), dP}
local notation "e" => DeltaStructure.frobeniusEquiv W.deltaStructure hW
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW})) (Ideal.Quotient.mk W.ideal)

/-- 概要：無限根入力の二元商と R/ϖ 上の同じ無限根環の同型。
方針：任意係数イデアル商との交換と逆係数 Frobenius を合成する。
規約：指数モノイドは変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の主分冪入力の係数移送。 -/
def powerRootFrobeniusPairVarpiInputEquiv : (P ⧸ KP) ≃+* Nv :=
  ((Ideal.quotEquivOfEq (show KP = (K).map (algebraMap A P) by
    rw [Ideal.map_span, Set.image_pair, map_natCast])).trans
      (powerRootCoefficientIdealQuotientEquiv A p hp K)).trans
    (AddMonoidAlgebra.mapRingEquiv G (perfectPrismVarpiToFrobeniusPairEquiv W hW).symm)

/-- 概要：入力同型は単項式の係数に逆 Frobenius を適用する。
方針：商比較とモノイド環の係数写像の公式を合成する。
規約：指数を変えない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の具体的係数作用の確認。 -/
theorem powerRootFrobeniusPairVarpiInputEquiv_single (q : G) (r : A) :
    powerRootFrobeniusPairVarpiInputEquiv W hW
      (Ideal.Quotient.mk KP (AddMonoidAlgebra.single q r)) =
        AddMonoidAlgebra.single q (barr ((e).symm r)) := by
  simp only [powerRootFrobeniusPairVarpiInputEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, powerRootCoefficientIdealQuotientEquiv_mk,
    powerRootCoefficientIdealQuotientMap_single, AddMonoidAlgebra.mapRingEquiv_single,
    perfectPrismVarpiToFrobeniusPairEquiv_symm_mk]

/-- 概要：入力同型の標準係数上の公式。
方針：零指数の単項式を計算する。
規約：元の全ての係数を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の pd 係数作用の移送。 -/
theorem powerRootFrobeniusPairVarpiInputEquiv_coeff (r : A) :
    powerRootFrobeniusPairVarpiInputEquiv W hW
      (Ideal.Quotient.mk KP (algebraMap A P r)) = algebraMap Rv Nv (barr ((e).symm r)) := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using
    powerRootFrobeniusPairVarpiInputEquiv_single W hW 0 r

/-- 概要：入力同型は全ての根変数の番号を保つ。
方針：係数 1 の単項式の比較を使う。
規約：全ての段 n を含める。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の一元多項式評価の比較。 -/
theorem powerRootFrobeniusPairVarpiInputEquiv_variable (n : ℕ) :
    powerRootFrobeniusPairVarpiInputEquiv W hW
      (Ideal.Quotient.mk KP (powerRootPolynomialVariable A p hp n)) =
        powerRootPolynomialVariable Rv p hp n := by
  simpa only [powerRootPolynomialVariable, map_one] using
    powerRootFrobeniusPairVarpiInputEquiv_single W hW _ 1

/-- 概要：元の無限根環から ϖ 係数の無限根環への通常比較射。
方針：二元商射と入力同型を合成する。
規約：逆 Frobenius 係数作用を持つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の評価の自然性を適用するための環射。 -/
def powerRootFrobeniusPairVarpiInputMap : P →+* Nv :=
  (powerRootFrobeniusPairVarpiInputEquiv W hW).toRingHom.comp (Ideal.Quotient.mk KP)

/-- 概要：通常入力多項式は逆 Frobenius で係数変更した評価へ送られる。
方針：評価の自然性と標準係数・根変数の公式を使う。
規約：モニック性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の主分冪表示の正確な入力。 -/
theorem powerRootFrobeniusPairVarpiInputEquiv_baseMap (f : Polynomial A) :
    powerRootFrobeniusPairVarpiInputEquiv W hW
      (Ideal.Quotient.mk KP (powerRootPolynomialBaseMap A p hp f)) =
        powerRootPolynomialBaseMap Rv p hp
          ((perfectPrismInverseFrobeniusPolynomial W hW f).map barr) := by
  let F := powerRootFrobeniusPairVarpiInputMap W hW
  change F (powerRootPolynomialBaseMap A p hp f) = _
  unfold powerRootPolynomialBaseMap
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def,
    show F (powerRootPolynomialVariable A p hp 0) = powerRootPolynomialVariable Rv p hp 0 from
      powerRootFrobeniusPairVarpiInputEquiv_variable W hW 0,
    perfectPrismInverseFrobeniusPolynomial, Polynomial.eval₂_map, Polynomial.eval₂_map]
  congr 1
  apply RingHom.ext
  intro r
  exact powerRootFrobeniusPairVarpiInputEquiv_coeff W hW r

/-- 概要：名前付きモニック入力も同じ逆 Frobenius 係数評価へ送られる。
方針：入力の定義を一度展開して評価公式を使う。
規約：元の多項式を暗黙に変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の標準主 pd 同型への入力等式。 -/
theorem powerRootFrobeniusPairVarpiInputEquiv_input (f : Polynomial A) :
    powerRootFrobeniusPairVarpiInputEquiv W hW
      (Ideal.Quotient.mk KP (powerRootMonicPDInput p f)) =
        powerRootPolynomialBaseMap Rv p hp
          ((perfectPrismInverseFrobeniusPolynomial W hW f).map barr) := by
  unfold powerRootMonicPDInput
  exact powerRootFrobeniusPairVarpiInputEquiv_baseMap W hW f

end SerrePositivity.BhattScholze.Andre

end PowerRootFrobeniusPairVarpiInput

/-! ## モニック入力の実 pd 包の任意係数還元

## 概要

完全 prism 上の無限根モニック入力の実 pd 包は、任意の mod p 係数元で還元しても
実分冪構造を持つ。BS 著者版 Remark 7.15(1)（著者版 p.62）の係数変更。

## 方針

正次数商の係数環上の自由性から射影性を得て、係数主イデアルとの交わりを制御する。
原典とは異なる線形切断による分冪降下を使う。

## 規約

還元する係数元にも prism 商にも正則性を要求しない。入力のモニック性は保持する。

## 使われ方

ϖ 持上げによる還元を、prism 商の p 正則性を使わずに構成する。
-/

@[expose] public noncomputable section PowerRootCoefficientPDProjectiveReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "R" => A ⧸ Ideal.span {(p : A)}
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "N" => PowerRootPolynomial R p hp
local notation "z" f => powerRootCoefficientPDInput p f
local notation "D" f => PowerRootCoefficientPDEnvelope p f
local notation "J" f => principalDPPositiveIdeal (z f)

/-- 概要：無限根モニック pd 包の構造は任意係数元の商へ降りる。
方針：正次数商の自由性から射影性を供給し、一般の係数商の実分冪構造を使う。
規約：係数元の正則性も prism 商の p 正則性も仮定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）のモニック入力の無条件の係数還元。 -/
def powerRootCoefficientPDReductionOfMonic
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (a : R) :
    DividedPowers ((J f).map (Ideal.Quotient.mk (Ideal.span {algebraMap R (D f) a}))) := by
  let := powerRootCoefficientPDPositiveQuotient_free p f hf
  exact dividedPowersQuotientOfProjectiveCoefficient
    (powerRootCoefficientDividedPowers p W hW f hf) a

/-- 概要：任意係数還元後の入力元の分冪は元の標準生成元の商像。
方針：係数商の分冪評価と還元前の入力分冪の公式を合成する。
規約：全次数 n を含み、係数元には制約しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の還元後の pd 普遍性への入力。 -/
theorem powerRootCoefficientPDReductionOfMonic_base_apply
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (a : R) (n : ℕ) :
    (powerRootCoefficientPDReductionOfMonic p W hW f hf a).dpow n
      (Ideal.Quotient.mk _ (algebraMap N (D f) (z f))) =
      Ideal.Quotient.mk _ (principalDPGenerator (z f) n) := by
  let := powerRootCoefficientPDPositiveQuotient_free p f hf
  unfold powerRootCoefficientPDReductionOfMonic
  rw [dividedPowersQuotientOfProjectiveCoefficient_apply _ _ n
    (principalDPPositiveIdeal_base_mem (z f)), powerRootCoefficientDividedPowers_base_apply]

/-- 概要：任意係数元によるモニック pd 包の標準商射は分冪射。
方針：射影的な正次数商を使う分冪商の互換性を適用する。
規約：還元前と還元後の実分冪構造を使う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の任意係数還元の構造比較。 -/
theorem powerRootCoefficientPDReductionOfMonic_isDPMorphism
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (a : R) :
    (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism
      (powerRootCoefficientPDReductionOfMonic p W hW f hf a)
      (Ideal.Quotient.mk (Ideal.span {algebraMap R (D f) a})) := by
  let := powerRootCoefficientPDPositiveQuotient_free p f hf
  exact dividedPowersQuotientOfProjectiveCoefficient_isDPMorphism
    (powerRootCoefficientDividedPowers p W hW f hf) a

end SerrePositivity.BhattScholze.Andre

end PowerRootCoefficientPDProjectiveReduction

/-! ## 係数 Frobenius と指数 Frobenius の分離

## 概要

完全 δ 係数環上の無限根環の Frobenius は、係数 Frobenius と指数 p 倍の
互いに可換な二つの δ 自己同型の合成。
BS 著者版 Remark 7.15（著者版 p.62）の φ_A による係数変更と変数の作用を区別する。

## 方針

モノイド環の係数同型と指数同型を別々に束ね、可換性を既存の写像の自然性で示す。
p 正則性の下で Frobenius との可換性から δ 射であることを得る。

## 規約

係数同型は全根変数を固定し、指数同型は係数を固定する。未完備の環を扱う。

## 使われ方

prismatic envelope の raw 包の係数変更を、入力多項式と変数を追跡して比較する。
-/

@[expose] public noncomputable section PowerRootFrobeniusFactors

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => powerRootExponentMonoid p hp
local notation "P" => PowerRootPolynomial A p hp
variable (D : DeltaStructure p A) (hD : D.IsPerfect)

/-- 概要：係数 Frobenius のみを適用する無限根環の環同型。
方針：係数環同型を加法モノイド環へ持ち上げる。
規約：単項式の指数は固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の φ_A による係数作用。 -/
def powerRootCoefficientFrobeniusEquiv : P ≃+* P :=
  AddMonoidAlgebra.mapRingEquiv G (D.frobeniusEquiv hD)

/-- 概要：指数の p 倍のみを適用する無限根環の環同型。
方針：指数加法同型をモノイド環へ持ち上げる。
規約：係数を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全体 Frobenius の変数成分。 -/
def powerRootVariableFrobeniusEquiv : P ≃+* P :=
  AddMonoidAlgebra.mapDomainRingEquiv A (powerRootExponentPrimeScaleEquiv p)

/-- 概要：係数 Frobenius は単項式の係数だけを送る。
方針：係数環同型の単項式公式を使う。
規約：任意の指数・係数を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数と変数の分離。 -/
theorem powerRootCoefficientFrobeniusEquiv_single (q : G) (b : A) :
    powerRootCoefficientFrobeniusEquiv p D hD (AddMonoidAlgebra.single q b) =
      AddMonoidAlgebra.single q (D.frobeniusLift b) :=
  AddMonoidAlgebra.mapRingEquiv_single _ _ _

/-- 概要：指数 Frobenius は単項式の指数だけを p 倍する。
方針：指数同型の単項式公式を使う。
規約：係数は同じ元を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の指数作用。 -/
theorem powerRootVariableFrobeniusEquiv_single (q : G) (b : A) :
    powerRootVariableFrobeniusEquiv (A := A) p (AddMonoidAlgebra.single q b) =
      AddMonoidAlgebra.single (p • q) b :=
  AddMonoidAlgebra.mapDomainRingEquiv_single _ _ _

/-- 概要：係数 Frobenius は元の係数の標準像をその Frobenius 像へ送る。
方針：零指数の単項式で計算する。
規約：標準係数射を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数作用の照合。 -/
theorem powerRootCoefficientFrobeniusEquiv_coeff (b : A) :
    powerRootCoefficientFrobeniusEquiv p D hD (algebraMap A P b) =
      algebraMap A P (D.frobeniusLift b) := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using
    powerRootCoefficientFrobeniusEquiv_single p D hD 0 b

/-- 概要：係数 Frobenius は全ての根変数を固定する。
方針：係数 1 の単項式で計算する。
規約：全ての段 n を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力多項式の係数変更。 -/
theorem powerRootCoefficientFrobeniusEquiv_variable (n : ℕ) :
    powerRootCoefficientFrobeniusEquiv p D hD (powerRootPolynomialVariable A p hp n) =
      powerRootPolynomialVariable A p hp n := by
  simp only [powerRootPolynomialVariable, powerRootCoefficientFrobeniusEquiv_single, map_one]

/-- 概要：指数 Frobenius は元の係数の標準像を固定する。
方針：零指数の単項式で計算する。
規約：係数環 A の全ての元を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の A 線形な変数作用。 -/
theorem powerRootVariableFrobeniusEquiv_coeff (b : A) :
    powerRootVariableFrobeniusEquiv (A := A) p (algebraMap A P b) = algebraMap A P b := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using
    powerRootVariableFrobeniusEquiv_single p (0 : G) b

/-- 概要：指数 Frobenius は各根変数をその p 乗へ送る。
方針：単項式の冪と指数 p 倍の公式を使う。
規約：全ての段 n を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の変数の再配置。 -/
theorem powerRootVariableFrobeniusEquiv_variable (n : ℕ) :
    powerRootVariableFrobeniusEquiv (A := A) p (powerRootPolynomialVariable A p hp n) =
      powerRootPolynomialVariable A p hp n ^ p := by
  simp only [powerRootPolynomialVariable, powerRootVariableFrobeniusEquiv_single,
    AddMonoidAlgebra.single_pow, one_pow]

/-- 概要：係数と指数の Frobenius は環射として可換。
方針：モノイド環の係数写像と指数写像の自然性を使う。
規約：両側の合成順序を環射の等式で明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の δ 互換性の判定。 -/
theorem powerRootFrobeniusFactors_commute :
    (powerRootCoefficientFrobeniusEquiv p D hD).toRingHom.comp
      (powerRootVariableFrobeniusEquiv (A := A) p).toRingHom =
    (powerRootVariableFrobeniusEquiv (A := A) p).toRingHom.comp
      (powerRootCoefficientFrobeniusEquiv p D hD).toRingHom :=
  AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom D.frobeniusLift (powerRootExponentPrimeScale p)

/-- 概要：全体 Frobenius は係数成分の後に指数成分を適用したもの。
方針：既存の標準 Frobenius の定義を使う。
規約：既存 δ 構造の Frobenius を変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二つの作用の正確な関係。 -/
theorem powerRootFrobeniusFactors_apply (t : P) :
    powerRootVariableFrobeniusEquiv (A := A) p (powerRootCoefficientFrobeniusEquiv p D hD t) =
      powerRootPolynomialFrobenius p D t := rfl

/-- 概要：係数 Frobenius 成分は標準無限根 δ 構造の δ 自己同型。
方針：全体 Frobenius との可換性を p 正則性の下で δ 互換性に戻す。
規約：既存の δ 構造を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数変更を raw δ 包へ適用する入力。 -/
theorem powerRootCoefficientFrobeniusEquiv_isDeltaHom :
    (powerRootPolynomialDelta p hD.p_mul_injective D).IsDeltaHom
      (powerRootPolynomialDelta p hD.p_mul_injective D)
      (powerRootCoefficientFrobeniusEquiv p D hD).toRingHom := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _
    (powerRootPolynomial_primeRegular p hD.p_mul_injective)
  intro t
  rw [powerRootPolynomialDelta_frobenius]
  exact RingHom.congr_fun (powerRootFrobeniusFactors_commute p D hD)
    (powerRootCoefficientFrobeniusEquiv p D hD t)

/-- 概要：指数 Frobenius 成分も標準無限根 δ 構造の δ 自己同型。
方針：係数成分との可換性を全体 Frobenius との可換性にし、p 正則性を使う。
規約：係数環の完全性から p 正則性を供給する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の変数成分を raw δ 包へ適用する入力。 -/
theorem powerRootVariableFrobeniusEquiv_isDeltaHom :
    (powerRootPolynomialDelta p hD.p_mul_injective D).IsDeltaHom
      (powerRootPolynomialDelta p hD.p_mul_injective D)
      (powerRootVariableFrobeniusEquiv (A := A) p).toRingHom := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _
    (powerRootPolynomial_primeRegular p hD.p_mul_injective)
  intro t
  rw [powerRootPolynomialDelta_frobenius]
  exact congrArg (powerRootVariableFrobeniusEquiv (A := A) p)
    (RingHom.congr_fun (powerRootFrobeniusFactors_commute p D hD) t).symm

/-- 概要：係数 Frobenius は通常多項式の係数だけを Frobenius で送って評価する。
方針：評価の自然性と係数・変数の公式を使う。
規約：モニック性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の φ_A 係数変更後の f の追跡。 -/
theorem powerRootCoefficientFrobeniusEquiv_baseMap (f : Polynomial A) :
    powerRootCoefficientFrobeniusEquiv p D hD (powerRootPolynomialBaseMap A p hp f) =
      powerRootPolynomialBaseMap A p hp (f.map D.frobeniusLift) := by
  unfold powerRootPolynomialBaseMap
  change (powerRootCoefficientFrobeniusEquiv p D hD).toRingHom
    (Polynomial.eval₂ (algebraMap A P) (powerRootPolynomialVariable A p hp 0) f) = _
  rw [Polynomial.hom_eval₂]
  change Polynomial.eval₂ _
    (powerRootCoefficientFrobeniusEquiv p D hD (powerRootPolynomialVariable A p hp 0)) f = _
  rw [powerRootCoefficientFrobeniusEquiv_variable, Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  apply RingHom.ext
  intro b
  exact powerRootCoefficientFrobeniusEquiv_coeff p D hD b

/-- 概要：二成分の合成同型は既存 δ 構造の Frobenius 同型そのもの。
方針：各元上で全体 Frobenius と一致することを使い環同型の外延性を適用する。
規約：完全性証明は既存の無限根 δ 完全性を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数成分と以前の全体比較の接続。 -/
theorem powerRootFrobeniusFactors_equiv :
    (powerRootCoefficientFrobeniusEquiv p D hD).trans
      (powerRootVariableFrobeniusEquiv (A := A) p) =
    (powerRootPolynomialDelta p hD.p_mul_injective D).frobeniusEquiv
      (powerRootPolynomialDelta_isPerfect p D hD) := by
  apply RingEquiv.ext
  intro t
  change powerRootVariableFrobeniusEquiv (A := A) p
    (powerRootCoefficientFrobeniusEquiv p D hD t) =
      (powerRootPolynomialDelta p hD.p_mul_injective D).frobeniusLift t
  rw [powerRootPolynomialDelta_frobenius]
  exact powerRootFrobeniusFactors_apply p D hD t

/-- 概要：指数成分は通常多項式の係数を保ち、通常変数だけを p 乗にする。
方針：多項式評価の自然性と係数・変数の計算公式を使う。
規約：任意の多項式を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数引戻し後の変数再配置。 -/
theorem powerRootVariableFrobeniusEquiv_baseMap (f : Polynomial A) :
    powerRootVariableFrobeniusEquiv (A := A) p (powerRootPolynomialBaseMap A p hp f) =
      Polynomial.eval₂ (algebraMap A P) (powerRootPolynomialVariable A p hp 0 ^ p) f := by
  unfold powerRootPolynomialBaseMap
  change (powerRootVariableFrobeniusEquiv (A := A) p).toRingHom
    (Polynomial.eval₂ (algebraMap A P) (powerRootPolynomialVariable A p hp 0) f) = _
  rw [Polynomial.hom_eval₂]
  change Polynomial.eval₂ _
    (powerRootVariableFrobeniusEquiv (A := A) p (powerRootPolynomialVariable A p hp 0)) f = _
  rw [powerRootVariableFrobeniusEquiv_variable]
  congr 1
  apply RingHom.ext
  intro b
  exact powerRootVariableFrobeniusEquiv_coeff p b

end SerrePositivity.BhattScholze.Andre

end PowerRootFrobeniusFactors

/-! ## 具体的な無限根多項式環の普遍性

## 概要

任意の係数環射と互換な p 冪根列に対し、現在の単項式表示の無限根多項式環から
係数と全根を保つ環射が一意に存在する。BS 著者版 Remark 7.15（著者版 p.62）の入力環。

## 方針

有理指数を根列で評価するモノイド射を加法モノイド環へ延長する。
一意性は各単項式が一つの有限段の根変数の冪になることから従う。
原典の記述を補う具体的な有理指数による経路。

## 規約

p の正値性だけを仮定し、終域の標数・正則性・完備性は制限しない。

## 使われ方

prismatic envelope の入力射を、根の像を指定するデータから作る。
-/

@[expose] public noncomputable section PowerRootPolynomialUniversal

namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) (hp : 0 < p)
variable {B : Type v} [CommRing B]
local notation "P" => PowerRootPolynomial R p hp

/-- 概要：無限根多項式環の環射は係数と全根変数の像で決まる。
方針：単項式を一つの根変数の冪に表し、単項式による加法的生成を使う。
規約：終域には任意の可換環を許す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力射の一意性。 -/
theorem powerRootPolynomial_ringHom_ext (F G : P →+* B)
    (hcoeff : F.comp (algebraMap R P) = G.comp (algebraMap R P))
    (hroot : ∀ n, F (powerRootPolynomialVariable R p hp n) =
      G (powerRootPolynomialVariable R p hp n)) : F = G := by
  apply RingHom.ext
  intro x
  induction x using AddMonoidAlgebra.induction_on with
  | of q =>
    obtain ⟨n, k, h⟩ := powerRootPolynomial_single_exists R p hp q 1
    simp only [map_one, one_mul] at h
    change F (AddMonoidAlgebra.single q 1) = G (AddMonoidAlgebra.single q 1)
    rw [h, map_pow, map_pow, hroot]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul a x hx =>
    have ha : F (algebraMap R P a) = G (algebraMap R P a) := RingHom.congr_fun hcoeff a
    rw [Algebra.smul_def, map_mul, map_mul, ha, hx]

variable (f : R →+* B) (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)

/-- 概要：指定した互換根列への無限根多項式の評価射。
方針：指数のモノイド射と係数環射を加法モノイド環の普遍射へ渡す。
規約：元の具体的な無限根多項式環を源とする。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根データからの実入力射。 -/
def powerRootPolynomialEval : P →+* B :=
  AddMonoidAlgebra.liftNCRingHom f (powerRootExponentEvalHom p hp ρ hρ)
    (fun _ _ => Commute.all _ _)

/-- 概要：無限根評価射は元の係数を指定係数射へ送る。
方針：零指数の単項式を評価し、モノイド射の単位保存性を使う。
規約：全ての係数元を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底環上の普遍性。 -/
theorem powerRootPolynomialEval_coeff (a : R) :
    powerRootPolynomialEval p hp f ρ hρ (algebraMap R P a) = f a := by
  change AddMonoidAlgebra.liftNCRingHom f (powerRootExponentEvalHom p hp ρ hρ) _
    (AddMonoidAlgebra.single 0 a) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  change f a * (powerRootExponentEvalHom p hp ρ hρ) 1 = f a
  rw [map_one, mul_one]

/-- 概要：無限根評価射は全ての根変数を指定根列へ送る。
方針：係数 1 の単項式の評価と指数モノイド射の変数公式を使う。
規約：全段 n の元の根の像を保つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根付き入力射の照合。 -/
theorem powerRootPolynomialEval_variable (n : ℕ) :
    powerRootPolynomialEval p hp f ρ hρ (powerRootPolynomialVariable R p hp n) = ρ n := by
  change AddMonoidAlgebra.liftNCRingHom f (powerRootExponentEvalHom p hp ρ hρ) _
    (AddMonoidAlgebra.single _ 1) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single, map_one, one_mul,
    powerRootExponentEvalHom_variable]

include hρ in
/-- 概要：係数と互換な根列を保つ無限根多項式環からの環射は一意に存在。
方針：具体的評価射を証人とし、係数・全根変数による外延性を使う。
規約：prism・分冪構造・完備性の仮定は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の指定 δ 射を根データで構成する準備。 -/
theorem existsUnique_powerRootPolynomialHom :
    ∃! F : P →+* B,
      F.comp (algebraMap R P) = f ∧
        ∀ n, F (powerRootPolynomialVariable R p hp n) = ρ n := by
  have hc : (powerRootPolynomialEval p hp f ρ hρ).comp (algebraMap R P) = f := by
    apply RingHom.ext
    exact powerRootPolynomialEval_coeff p hp f ρ hρ
  refine ⟨powerRootPolynomialEval p hp f ρ hρ,
    ⟨hc, powerRootPolynomialEval_variable p hp f ρ hρ⟩, ?_⟩
  intro F hF
  apply powerRootPolynomial_ringHom_ext p hp F _ (hF.1.trans hc.symm)
  intro n
  exact (hF.2 n).trans (powerRootPolynomialEval_variable p hp f ρ hρ n).symm

end SerrePositivity.BhattScholze.Andre

end PowerRootPolynomialUniversal

/-! ## 無限根の方程式商の入力射

## 概要

通常の商 R[Y^(1/p^∞)]/(f(Y)) からの環射は、係数射と f を消す互換根列で一意に決まる。
BS 著者版 Remark 7.15（著者版 p.62）の完備入力環 S に接続するための未完備入力環。

## 方針

具体的な無限根多項式の評価射を主イデアルで降下し、係数と根による外延性を使う。
原典の記述を補う、単項式表示と通常の商の普遍性による経路。

## 規約

この段階は通常の商だけを扱う。完備化や原典の S との同定は主張しない。
モニック性・正次数・素数性は不要で、p の正値性だけを要求する。

## 使われ方

prismatic envelope の試験データを、個別の根列から実際の入力環の射へ変換する。
-/

@[expose] public noncomputable section PowerRootEquationQuotient

namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) (hp : 0 < p) (f : Polynomial R)
local notation "P" => PowerRootPolynomial R p hp
local notation "I" => Ideal.span {powerRootPolynomialBaseMap R p hp f}

/-- 概要：無限根多項式環を f(Y) = 0 で割った通常の入力環。
方針：第零変数での多項式評価が生成する主イデアルで割る。
規約：完備化をまだ施さず、モニック性も不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の S への未完備入力。 -/
abbrev PowerRootEquationQuotient := P ⧸ I

/-- 概要：方程式商への係数環の標準射。
方針：無限根多項式環の係数射と商射を合成する。
規約：商上の algebra インスタンスの選択を必要としない環射。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底射を保つ入力データ。 -/
def powerRootEquationQuotientCoeff : R →+* PowerRootEquationQuotient p hp f :=
  (Ideal.Quotient.mk I).comp (algebraMap R P)

/-- 概要：方程式商内の全ての標準根変数。
方針：各 Yₙ を商射で写す。
規約：第零根が f の根になる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根列の標準入力。 -/
def powerRootEquationQuotientRoot (n : ℕ) : PowerRootEquationQuotient p hp f :=
  Ideal.Quotient.mk I (powerRootPolynomialVariable R p hp n)

/-- 概要：方程式商の標準根列は p 冪について互換。
方針：無限根多項式環の関係式を商射で写す。
規約：任意の係数環を許す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の試験射からの根列抽出。 -/
theorem powerRootEquationQuotientRoot_pow (n : ℕ) :
    powerRootEquationQuotientRoot p hp f (n + 1) ^ p = powerRootEquationQuotientRoot p hp f n := by
  unfold powerRootEquationQuotientRoot
  rw [← map_pow, powerRootPolynomialVariable_pow]

/-- 概要：方程式商の第零根は指定された f を消す。
方針：評価と商射の可換性から主イデアルの生成元の消滅に帰着する。
規約：定数多項式を含めて成り立つ。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力環内の方程式。 -/
theorem powerRootEquationQuotientRoot_equation :
    f.eval₂ (powerRootEquationQuotientCoeff p hp f)
      (powerRootEquationQuotientRoot p hp f 0) = 0 := by
  have h := Polynomial.hom_eval₂ f (algebraMap R P) (Ideal.Quotient.mk I)
    (powerRootPolynomialVariable R p hp 0)
  unfold powerRootEquationQuotientCoeff powerRootEquationQuotientRoot
  rw [← h]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)

variable {B : Type v} [CommRing B]

/-- 概要：方程式商からの環射は係数と全根の像で決まる。
方針：商射で引き戻し、無限根多項式環の外延性を適用する。
規約：終域には完備性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力射の一意性。 -/
theorem powerRootEquationQuotient_ringHom_ext (F G : PowerRootEquationQuotient p hp f →+* B)
    (hc : F.comp (powerRootEquationQuotientCoeff p hp f) =
      G.comp (powerRootEquationQuotientCoeff p hp f))
    (hr : ∀ n, F (powerRootEquationQuotientRoot p hp f n) =
      G (powerRootEquationQuotientRoot p hp f n)) : F = G := by
  apply Ideal.Quotient.ringHom_ext
  exact powerRootPolynomial_ringHom_ext p hp _ _ hc hr

/-- 概要：f を消す互換根列と係数射は方程式商からの一意な環射を与える。
方針：無限根評価射を生成元が消える主イデアルで降下し、外延性で一意性を得る。
規約：全ての根を同時に保存し、終域の正則性や完備性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根データと入力射の具体的な対応。 -/
theorem existsUnique_powerRootEquationQuotientHom (k : R →+* B)
    (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (hf : f.eval₂ k (ρ 0) = 0) :
    ∃! F : PowerRootEquationQuotient p hp f →+* B,
      F.comp (powerRootEquationQuotientCoeff p hp f) = k ∧
        ∀ n, F (powerRootEquationQuotientRoot p hp f n) = ρ n := by
  let g := powerRootPolynomialEval p hp k ρ hρ
  have heval : g (powerRootPolynomialBaseMap R p hp f) = 0 := by
    unfold powerRootPolynomialBaseMap
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, powerRootPolynomialEval_variable]
    have hc : g.comp (algebraMap R P) = k := by
      apply RingHom.ext
      exact powerRootPolynomialEval_coeff p hp k ρ hρ
    rw [hc]
    exact hf
  let F : PowerRootEquationQuotient p hp f →+* B := Ideal.Quotient.lift I g (by
    change I ≤ RingHom.ker g
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact heval)
  have hc : F.comp (powerRootEquationQuotientCoeff p hp f) = k := by
    apply RingHom.ext
    exact powerRootPolynomialEval_coeff p hp k ρ hρ
  have hr : ∀ n, F (powerRootEquationQuotientRoot p hp f n) = ρ n :=
    powerRootPolynomialEval_variable p hp k ρ hρ
  refine ⟨F, ⟨hc, hr⟩, ?_⟩
  intro K hK
  exact powerRootEquationQuotient_ringHom_ext p hp f K F (hK.1.trans hc.symm)
    (fun n => (hK.2 n).trans (hr n).symm)

end SerrePositivity.BhattScholze.Andre

end PowerRootEquationQuotient

/-! ## André A1-a：方程式商の p 完備化の普遍性

## 概要

通常の方程式商 R[Y^(1/p^∞)]/(f) の p 完備化から p 完備環への射は、
係数射と f を消す互換根列で一意に決まる。BS 著者版 Remark 7.15（著者版 p.62）の入力比較。

## 方針

通常の商の普遍性と p 完備化の環射の普遍性を続けて使う。
原典の記述を補う具体的な通常の商と完備化による経路。

## 規約

ここで完備化するのは通常の方程式商。完備多項式環を f で割る順序との交換は別工程。
源の p 正則性・モニック性・正次数は要求しない。

## 使われ方

完備入力環からの試験射を根データで扱う。
-/

@[expose] public noncomputable section PowerRootEquationCompletionUniversal

namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) (hp : 0 < p) (f : Polynomial R)
variable {B : Type v} [CommRing B] [IsAdicComplete (Ideal.span {(p : B)}) B]
local notation "S" => PowerRootEquationQuotient p hp f
local notation "C" => AdicCompletion (Ideal.span {(p : S)}) S
local notation "j" => algebraMap S C
local notation "c" => powerRootEquationQuotientCoeff p hp f
local notation "r" => powerRootEquationQuotientRoot p hp f

/-- 概要：方程式商の p 完備化からの射は係数と互換な方程式の根列で一意に定まる。
方針：通常の商からの一意な射を p 完備化へ一意に延長する。
規約：完備化前の入力根の自然像を全て保存する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備入力環からの試験射。 -/
theorem existsUnique_powerRootEquationCompletionHom (k : R →+* B)
    (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (hf : f.eval₂ k (ρ 0) = 0) :
    ∃! F : C →+* B, (F.comp j).comp c = k ∧ ∀ n, F (j (r n)) = ρ n := by
  obtain ⟨g, hg, hgu⟩ := existsUnique_powerRootEquationQuotientHom p hp f k ρ hρ hf
  obtain ⟨F, hF, hu⟩ := existsUnique_primeAdicCompletionHom S p g
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · rw [hF]
    exact hg.1
  · intro n
    exact (RingHom.congr_fun hF (r n)).trans (hg.2 n)
  · intro K hK
    exact hu K (hgu (K.comp j) ⟨hK.1, hK.2⟩)

end SerrePositivity.BhattScholze.Andre

end PowerRootEquationCompletionUniversal

/-! ## André A1-a：原典の順序による完備モニック入力環

## 概要

R⟨Y^(1/p^∞)⟩/(f) を、無限根多項式環の通常の p 完備化を f で割った環として定義する。
モニック f に対し、通常の方程式商の p 完備化と全入力元を保つ環同型を持つ。
BS 著者版 Remark 7.15（著者版 p.62）の S との接続。

## 方針

全係数 p 冪商でのモニック正則性を主商と完備化の交換定理へ供給する。
原典の記述を補う、係数主商・一様なフィルトレーション比較・普遍性による経路。

## 規約

係数環の p 正則性・有界ねじれ・p 完備性は要求せず、p の正値性とモニック性を使う。
この入力環の同定から源 H の prism 性までは結論しない。

## 使われ方

原典の順序の完備入力射を、検証済みの実完備化 H の普遍性へ渡す。
-/

@[expose] public noncomputable section PowerRootMonicCompletedInput

namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) (hp : 0 < p) (f : Polynomial R)
local notation "P" => PowerRootPolynomial R p hp
local notation "z" => powerRootPolynomialBaseMap R p hp f
local notation "CP" => AdicCompletion (Ideal.span {(p : P)}) P
local notation "jP" => algebraMap P CP
local notation "S₀" => PowerRootEquationQuotient p hp f
local notation "CS" => AdicCompletion (Ideal.span {(p : S₀)}) S₀

/-- 概要：無限根多項式環を p 完備化してから f で割った入力環。
方針：原典の括弧の順序を通常の完備化と主商で明示する。
規約：型の定義にはモニック性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の S=R⟨Y^(1/p^∞)⟩/(f)。 -/
abbrev PowerRootMonicCompletedInput := CP ⧸ Ideal.span {jP z}

/-- 概要：モニック入力では完備化してから割る環と、割ってから完備化する環は同型。
方針：モニック入力の全 p 冪商での正則性を完備化と主商の交換に使う。
規約：元の係数環の p 正則性は仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の原典の S を既存の完備入力へ接続する。 -/
def powerRootMonicCompletedInputEquiv (hf : f.Monic) :
    PowerRootMonicCompletedInput p hp f ≃+* CS :=
  primeAdicCompletionQuotientEquiv P p z
    (fun n => powerRootPolynomial_monic_mod_prime_power_regular R p hp f hf n)

/-- 概要：完備入力環の交換同型は元の無限根多項式の全ての像を保つ。
方針：一般の主商交換同型の係数公式を使う。
規約：係数元と全段の根変数もこの式に含まれる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の試験射と根の追跡。 -/
theorem powerRootMonicCompletedInputEquiv_coeff (hf : f.Monic) (x : P) :
    powerRootMonicCompletedInputEquiv p hp f hf
      (Ideal.Quotient.mk (Ideal.span {jP z}) (jP x)) =
        algebraMap S₀ CS (Ideal.Quotient.mk (Ideal.span {z}) x) :=
  primeAdicCompletionQuotientEquiv_coeff P p z
    (fun n => powerRootPolynomial_monic_mod_prime_power_regular R p hp f hf n) x

/-- 概要：原典の順序で作ったモニック完備入力環は p 完備。
方針：全 p 冪商でのモニック正則性と完備化後の主商の完備性を使う。
規約：係数環に p 正則性・有界ねじれを追加しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の S の通常の完備性。 -/
theorem powerRootMonicCompletedInput_isAdicComplete (hf : f.Monic) :
    IsAdicComplete (Ideal.span {(p : PowerRootMonicCompletedInput p hp f)})
      (PowerRootMonicCompletedInput p hp f) :=
  primeAdicCompletion_principal_quotient_isAdicComplete P p z
    (fun n => powerRootPolynomial_monic_mod_prime_power_regular R p hp f hf n)

end SerrePositivity.BhattScholze.Andre

end PowerRootMonicCompletedInput

/-! ## André A1-a：完備入力環からの環射の外延性

## 概要

原典の順序の完備入力環から p 完備環への環射は、係数と全根の像で決まる。
BS 著者版 Remark 7.15（著者版 p.62）の入力作用を含む比較。

## 方針

主商射、p 完備化、無限根多項式環の三つの外延性を順に適用する。
原典を補う明示的な係数・根による経路。

## 規約

この外延性にはモニック性は不要。標的の通常の p 完備性を要求する。

## 使われ方

全根の保存から、完備入力環全体での可換性を結論する。
-/

@[expose] public noncomputable section PowerRootMonicCompletedInputExt

namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) (hp : 0 < p) (f : Polynomial R)
variable {B : Type v} [CommRing B] [IsAdicComplete (Ideal.span {(p : B)}) B]
local notation "P" => PowerRootPolynomial R p hp
local notation "CP" => AdicCompletion (Ideal.span {(p : P)}) P
local notation "z" => powerRootPolynomialBaseMap R p hp f
local notation "SI" => PowerRootMonicCompletedInput p hp f
local notation "lS" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {algebraMap P CP z})) (algebraMap P CP)

/-- 概要：p 完備な標的への完備入力射は係数と全根の像で決まる。
方針：主商と完備化の外延性を通じて無限根多項式環の外延性へ帰着する。
規約：源のモニック性・標的の p 正則性は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全入力作用の保存。 -/
theorem powerRootMonicCompletedInput_ringHom_ext (F G : SI →+* B)
    (hc : (F.comp lS).comp (algebraMap R P) = (G.comp lS).comp (algebraMap R P))
    (hr : ∀ n, F (lS (powerRootPolynomialVariable R p hp n)) =
      G (lS (powerRootPolynomialVariable R p hp n))) : F = G := by
  apply Ideal.Quotient.ringHom_ext
  apply primeAdicCompletion_ringHom_ext P p
  exact powerRootPolynomial_ringHom_ext p hp _ _ hc hr

end SerrePositivity.BhattScholze.Andre

end PowerRootMonicCompletedInputExt

/-! ## rank 1 の互換根列による無限根 δ 射の普遍性

## 概要

互換根列の全ての δ が零なら、係数 δ 射と根列から一意な無限根 δ 射が得られる。
BS 著者版 Remark 7.15（著者版 p.62）の指定入力 δ 射を根データで構成する。

## 方針

二つの W₂ 切断の合成を係数・全根変数上で比較し、通常環射の外延性を使う。
原典の記述を補う有理指数の普遍射と Witt 座標による経路。

## 規約

係数環には無限根 δ 構造を定義する p 正則性を要求する。
終域の p 正則性・完備性・完全性は仮定しない。

## 使われ方

絶対 prismatic envelope との比較に向け、指定 δ 射を係数と根のデータから作る。
-/

@[expose] public noncomputable section PowerRootPolynomialDeltaUniversal

namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime]
variable {B : Type v} [CommRing B]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial R p hp

/-- 概要：無限根環からの環射が係数・全根変数上で δ と可換なら δ 射。
方針：二つの W₂ 切断の合成を通常環射の外延性と二つの Witt 座標で比較する。
規約：源の δ 構造は任意で、終域には p ねじれを許す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の無限根入力射の δ 条件。 -/
theorem isDeltaHom_powerRootPolynomial
    (D : DeltaStructure p P) (E : DeltaStructure p B) (g : P →+* B)
    (hcoeff : ∀ a : R, g (D.delta (algebraMap R P a)) = E.delta (g (algebraMap R P a)))
    (hroot : ∀ n, g (D.delta (powerRootPolynomialVariable R p hp n)) =
      E.delta (g (powerRootPolynomialVariable R p hp n))) : D.IsDeltaHom E g := by
  apply (D.isDeltaHom_iff_sectionHom_comp E g).mpr
  apply powerRootPolynomial_ringHom_ext p hp
  · apply RingHom.ext
    intro a
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      exact congrArg g (D.coeff_zero (algebraMap R P a)) |>.trans
        (E.coeff_zero (g (algebraMap R P a))).symm
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      exact hcoeff a
  · intro n
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      exact congrArg g (D.coeff_zero (powerRootPolynomialVariable R p hp n)) |>.trans
        (E.coeff_zero (g (powerRootPolynomialVariable R p hp n))).symm
    · simp only [RingHom.comp_apply, wittTwoMap_coeff]
      exact hroot n

/-- 概要：p 進分離な δ 環の互換根列は全て rank 1 である。
方針：後続の根を各 p 冪根の証人にし、既存の分離性による δ=0 判定を使う。
規約：終域の p 正則性や根列の非零性は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根データに課す δ 条件を自動で供給する。 -/
theorem compatiblePowerRoots_delta_eq_zero (E : DeltaStructure p B)
    [IsHausdorff (Ideal.span {(p : B)}) B]
    (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) : E.delta (ρ n) = 0 :=
  E.delta_eq_zero_of_has_pow_roots (ρ n) (fun m =>
    ⟨ρ (n + m), compatiblePowerRoots_iterate p ρ hρ n m⟩)

variable (hpR : Function.Injective (fun a : R => (p : R) * a))
variable (D : DeltaStructure p R) (E : DeltaStructure p B) (f : R →+* B)
variable (hf : D.IsDeltaHom E f) (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
variable (hδρ : ∀ n, E.delta (ρ n) = 0)

include hf hδρ in
/-- 概要：係数 δ 射と rank 1 の互換根列による評価射は δ 射。
方針：標準無限根 δ 構造の係数公式と根変数の δ=0 を一般の判定へ渡す。
規約：終域の p ねじれや完備性には制約しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根データからの実入力 δ 射。 -/
theorem powerRootPolynomialEval_isDeltaHom :
    (powerRootPolynomialDelta p hpR D).IsDeltaHom E (powerRootPolynomialEval p hp f ρ hρ) := by
  apply isDeltaHom_powerRootPolynomial p
  · intro a
    rw [← powerRootPolynomialDelta_coeff_isDeltaHom p hpR D a,
      powerRootPolynomialEval_coeff, powerRootPolynomialEval_coeff, hf a]
  · intro n
    rw [powerRootPolynomialDelta_variable, map_zero, powerRootPolynomialEval_variable, hδρ]

include hf hρ hδρ in
/-- 概要：係数と rank 1 の互換根列を保つ δ 射は一意に存在。
方針：具体的評価射の δ 性を存在側に使い、通常環射の外延性で一意性を得る。
規約：根の δ=0 と隣接根関係を明示し、prism の完備性や終域の正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の指定入力射を根データへ置き換える。 -/
theorem existsUnique_powerRootPolynomialDeltaHom :
    ∃! g : P →+* B,
      (powerRootPolynomialDelta p hpR D).IsDeltaHom E g ∧
        g.comp (algebraMap R P) = f ∧
          ∀ n, g (powerRootPolynomialVariable R p hp n) = ρ n := by
  obtain ⟨g, hg, hu⟩ := existsUnique_powerRootPolynomialHom p hp f ρ hρ
  have hgeval : g = powerRootPolynomialEval p hp f ρ hρ := by
    apply powerRootPolynomial_ringHom_ext p hp g _
    · apply RingHom.ext
      intro a
      exact (RingHom.congr_fun hg.1 a).trans (powerRootPolynomialEval_coeff p hp f ρ hρ a).symm
    · intro n
      exact (hg.2 n).trans (powerRootPolynomialEval_variable p hp f ρ hρ n).symm
  refine ⟨g, ⟨?_, hg⟩, ?_⟩
  · rw [hgeval]
    exact powerRootPolynomialEval_isDeltaHom p hpR D E f hf ρ hρ hδρ
  · intro k hk
    exact hu k hk.2

include hf hρ in
/-- 概要：p 進分離な終域の互換根列へ、係数と根を保つ δ 射が一意に存在する。
方針：全根の rank 1 性を分離性から導き、一般の根データの δ 普遍性を使う。
規約：終域の p 正則性を要求せず、δ=0 を追加引数に残さない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の分離な試験環への入力 δ 射。 -/
theorem existsUnique_powerRootPolynomialDeltaHom_of_isHausdorff
    [IsHausdorff (Ideal.span {(p : B)}) B] :
    ∃! g : P →+* B,
      (powerRootPolynomialDelta p hpR D).IsDeltaHom E g ∧
        g.comp (algebraMap R P) = f ∧
          ∀ n, g (powerRootPolynomialVariable R p hp n) = ρ n :=
  existsUnique_powerRootPolynomialDeltaHom p hpR D E f hf ρ hρ
    (compatiblePowerRoots_delta_eq_zero p E ρ hρ)

end SerrePositivity.BhattScholze.Andre

end PowerRootPolynomialDeltaUniversal

/-! ## 有界試験 prism の剰余根列からの無限根入力 δ 射

## 概要

有界試験 prism の剰余内にある互換根列と基底 δ 射から、
剰余根列を保つ無限根入力 δ 射が一意に存在する。
BS 著者版 Remark 7.15（著者版 p.62）の入力 δ 射の持上げの有界試験環での計算。

## 方針

共通完備商による根列の一意持上げを行い、p 進分離性で rank 1 性を供給する。
原典とは異なる Perfection モノイド同型・有理指数の評価・W₂ 切断による経路。

## 規約

試験 prism の完全性は要求せず、有界性を明示する。源の δ 環には p 正則性のみを要求する。
試験 prism の商の p 正則性や非零性を仮定しない。

## 使われ方

指定入力 δ 射を前提とせず、原典の剰余上の根データから実完備化への射を作る。
-/

@[expose] public noncomputable section PowerRootPolynomialBoundedPrismLift

namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime]
variable {B : Type v} [CommRing B]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial R p hp

/-- 概要：完全 prism の剰余互換根列を保つ無限根入力 δ 射は一意に存在。
方針：実根列への一意持上げと rank 1 根列の δ 普遍性を合成する。
規約：根列は商内に与え、台環内の根列や δ 条件を引数に残さない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有界試験 prism に対する入力射の一意持上げ。 -/
theorem existsUnique_powerRootPolynomialDeltaHom_of_boundedPrism_residue_roots
    (hpR : Function.Injective (fun x : R => (p : R) * x)) (D : DeltaStructure p R)
    (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (k : R →+* B) (hk : D.IsDeltaHom Q.deltaStructure k)
    (ρ : ℕ → B ⧸ Q.ideal) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    ∃! g : P →+* B,
      (powerRootPolynomialDelta p hpR D).IsDeltaHom Q.deltaStructure g ∧
        g.comp (algebraMap R P) = k ∧
          ∀ n, Ideal.Quotient.mk Q.ideal (g (powerRootPolynomialVariable R p hp n)) = ρ n := by
  let := _root_.SerrePositivity.BhattScholze.boundedPrism_isHausdorff_prime Q hB
  obtain ⟨σ, hσ, hσu⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_boundedPrismCompatibleRootsLift Q hB ρ hρ
  obtain ⟨g, hg, hu⟩ := existsUnique_powerRootPolynomialDeltaHom_of_isHausdorff p hpR D
    Q.deltaStructure k hk σ hσ.1
  refine ⟨g, ⟨hg.1, hg.2.1, ?_⟩, ?_⟩
  · intro n
    exact (congrArg (Ideal.Quotient.mk Q.ideal) (hg.2.2 n)).trans (hσ.2 n)
  · intro K hK
    let τ := fun n => K (powerRootPolynomialVariable R p hp n)
    have hτ : ∀ n, τ (n + 1) ^ p = τ n := by
      intro n
      exact (map_pow K _ p).symm.trans
        (congrArg K (powerRootPolynomialVariable_pow R p hp n))
    have hτσ : τ = σ := hσu τ ⟨hτ, hK.2.2⟩
    apply hu K
    exact ⟨hK.1, hK.2.1, fun n => congrFun hτσ n⟩

end SerrePositivity.BhattScholze.Andre

end PowerRootPolynomialBoundedPrismLift

/-! ## 完全試験 prism の剰余根列からの無限根入力 δ 射

## 概要

完全試験 prism の剰余内にある互換根列と基底 δ 射から、
剰余根列を保つ無限根入力 δ 射が一意に存在する。
BS 著者版 Remark 7.15（著者版 p.62）の入力 δ 射の持上げの完全試験環での計算。

## 方針

共通完備商による根列の一意持上げを行い、p 進分離性で rank 1 性を供給する。
原典とは異なる Perfection モノイド同型・有理指数の評価・W₂ 切断による経路。

## 規約

完全性を要求するのは試験 prism。源の δ 環には p 正則性のみを要求する。
試験 prism の商の p 正則性や非零性を仮定しない。

## 使われ方

指定入力 δ 射を前提とせず、原典の剰余上の根データから実完備化への射を作る。
-/

@[expose] public noncomputable section PowerRootPolynomialPrismLift

namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime]
variable {B : Type v} [CommRing B]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial R p hp

/-- 概要：完全 prism の剰余互換根列を保つ無限根入力 δ 射は一意に存在。
方針：実根列への一意持上げと rank 1 根列の δ 普遍性を合成する。
規約：根列は商内に与え、台環内の根列や δ 条件を引数に残さない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完全試験 prism に対する入力射の一意持上げ。 -/
theorem existsUnique_powerRootPolynomialDeltaHom_of_perfectPrism_residue_roots
    (hpR : Function.Injective (fun x : R => (p : R) * x)) (D : DeltaStructure p R)
    (Q : OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)
    (k : R →+* B) (hk : D.IsDeltaHom Q.deltaStructure k)
    (ρ : ℕ → B ⧸ Q.ideal) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    ∃! g : P →+* B,
      (powerRootPolynomialDelta p hpR D).IsDeltaHom Q.deltaStructure g ∧
        g.comp (algebraMap R P) = k ∧
          ∀ n, Ideal.Quotient.mk Q.ideal (g (powerRootPolynomialVariable R p hp n)) = ρ n := by
  let := Q.isAdicComplete_p_of_perfect hQ
  obtain ⟨σ, hσ, hσu⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismCompatibleRootsLift Q hQ ρ hρ
  obtain ⟨g, hg, hu⟩ := existsUnique_powerRootPolynomialDeltaHom_of_isHausdorff p hpR D
    Q.deltaStructure k hk σ hσ.1
  refine ⟨g, ⟨hg.1, hg.2.1, ?_⟩, ?_⟩
  · intro n
    exact (congrArg (Ideal.Quotient.mk Q.ideal) (hg.2.2 n)).trans (hσ.2 n)
  · intro K hK
    let τ := fun n => K (powerRootPolynomialVariable R p hp n)
    have hτ : ∀ n, τ (n + 1) ^ p = τ n := by
      intro n
      exact (map_pow K _ p).symm.trans
        (congrArg K (powerRootPolynomialVariable_pow R p hp n))
    have hτσ : τ = σ := hσu τ ⟨hτ, hK.2.2⟩
    apply hu K
    exact ⟨hK.1, hK.2.1, fun n => congrFun hτσ n⟩

end SerrePositivity.BhattScholze.Andre

end PowerRootPolynomialPrismLift
