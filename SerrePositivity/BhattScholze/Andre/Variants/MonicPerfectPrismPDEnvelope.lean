module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrimeFrobeniusPDEnvelope
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootCoefficientPDProjectiveReduction

/-!
# André E1・E2：prism 商の p 正則性を使わないモニック pd 包

## 概要

完全 prism 上のモニック入力について、R/ϖ と R/p の無限根標準表示に
実分冪構造・入力分冪公式・pd 普遍性を与える。
BS Rem 7.15(1)（著者版 p.62）の係数還元における追加正則性を解消する。

## 方針

正次数商の自由性から任意係数元による分冪降下を使い、ϖ の持上げで還元する。
原典とは異なる線形切断・実環同型・分冪構造の移送による証明。

## 規約

完全 prism と入力のモニック性のみを使い、prism 商の p 正則性・正次数を仮定しない。
二つの係数環を明示し、mod p 側の入力は元の f の係数像とする。

## 使われ方

A 全体の実 Frobenius 引戻しに、追加正則性なしの実分冪構造と pd 普遍性を供給する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
section Native
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "N" => PowerRootPolynomial R₀ p hp
local notation "z" => powerRootCoefficientPDInput p f
local notation "D" => PowerRootCoefficientPDEnvelope p f
local notation "a" => Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)
local notation "K" => Ideal.span {algebraMap R₀ D a}
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zv" => powerRootPolynomialBaseMap Rv p hp (f.map barr)
local notation "Dv" => PrincipalDPPresentation Nv zv

/-- 概要：原典の係数環上のモニック入力の標準表示に実分冪構造を与える。
方針：射影的な正次数商により還元した構造を表示環同型で移す。
規約：prism 商の p 正則性を要求せず、モニック性のみを使う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の構造。 -/
def perfectPrismVarpiNativeDividedPowersOfMonic
    (hf : f.Monic) :
    DividedPowers (principalDPPositiveIdeal zv) :=
  DividedPowers.ofRingEquiv (perfectPrismVarpiPDEnvelopeEquiv_positiveIdeal W hW f)
    (powerRootCoefficientPDReductionOfMonic p W hW f hf a)

/-- 概要：原典の係数環上でも入力元の分冪は全標準生成元に一致する。
方針：移送公式と還元前の標準値の公式、同型の入力・生成元の比較を使う。
規約：全次数 n を含む。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 普遍性への入力。 -/
theorem perfectPrismVarpiNativeDividedPowersOfMonic_base_apply
    (hf : f.Monic) (n : ℕ) :
    (perfectPrismVarpiNativeDividedPowersOfMonic W hW f hf).dpow n
      (algebraMap Nv Dv zv) = principalDPGenerator zv n := by
  rw [← perfectPrismVarpiPDEnvelopeEquiv_input W hW f,
    perfectPrismVarpiNativeDividedPowersOfMonic, DividedPowers.ofRingEquiv_dpow_apply,
    powerRootCoefficientPDReductionOfMonic_base_apply,
    perfectPrismVarpiPDEnvelopeEquiv_generator]

/-- 概要：原典の係数環上の実 pd 包から任意の分冪標的への射は一意に存在する。
方針：移送済みの実分冪構造と標準値を一般の pd 普遍性へ供給する。
規約：標的は無限根環 Nv の任意の代数。
使われ方：BS Rem 7.15(1)（著者版 p.62）のモニック入力の実 pd 包の同定。 -/
theorem existsUnique_perfectPrismVarpiNativePDMorphismOfMonic
    (hf : f.Monic)
    {B : Type v} [CommRing B] [Algebra Nv B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap Nv B zv ∈ I) :
    ∃! F : Dv →ₐ[Nv] B,
      (perfectPrismVarpiNativeDividedPowersOfMonic W hW f hf).IsDPMorphism Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism zv
    (perfectPrismVarpiNativeDividedPowersOfMonic W hW f hf)
    (perfectPrismVarpiNativeDividedPowersOfMonic_base_apply W hW f hf) Ht hzB

end Native

section Prime
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => powerRootExponentMonoid p hp
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Rp" => (A ⧸ W.ideal) ⧸ Ideal.span {(p : A ⧸ W.ideal)}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "Np" => PowerRootPolynomial Rp p hp
local notation "evp" => perfectPrismVarpiFrobeniusQuotientEquiv W hW
local notation "bv" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "bp" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ W.ideal)}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "frob" => DeltaStructure.frobeniusEquiv W.deltaStructure hW

variable (f : Polynomial A)
local notation "zv" => powerRootPolynomialBaseMap Rv p hp
  (Polynomial.map bv (perfectPrismInverseFrobeniusPolynomial W hW f))
local notation "zp" => powerRootPolynomialBaseMap Rp p hp (Polynomial.map bp f)
local notation "Dv" => PrincipalDPPresentation Nv zv
local notation "Dp" => PrincipalDPPresentation Np zp

local notation "fInv" => perfectPrismInverseFrobeniusPolynomial W hW f
local notation "hMonicInv" => perfectPrismInverseFrobeniusPolynomial_monic W hW f
local notation "rootEq" => powerRootVarpiPrimeFrobeniusEquiv W hW
local notation "hInput" => powerRootVarpiPrimeFrobeniusEquiv_input W hW f

/-- 概要：元の mod p 入力の標準表示は実分冪構造を持つ。
方針：逆係数入力の実分冪構造を入力を保つ係数環同型で移す。
規約：prism 商の p 正則性を要求せず、モニック性のみを使う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の同定。 -/
def powerRootPrimeFrobeniusDividedPowersOfMonic
    (hf : f.Monic) :
    DividedPowers (principalDPPositiveIdeal zp) :=
  principalDPTransportDividedPowers rootEq zv zp hInput
    (perfectPrismVarpiNativeDividedPowersOfMonic W hW fInv (hMonicInv hf))

/-- 概要：元の入力の n 次分冪は n 次標準生成元。
方針：入力を保つ係数移送の分冪公式と元の標準値を使う。
規約：零次数を含む全次数を扱う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 普遍性の入力。 -/
theorem powerRootPrimeFrobeniusDividedPowersOfMonic_base_apply
    (hf : f.Monic) (n : ℕ) :
    (powerRootPrimeFrobeniusDividedPowersOfMonic W hW f hf).dpow n
      (algebraMap Np Dp zp) = principalDPGenerator zp n :=
  principalDPTransportDividedPowers_base_apply rootEq zv zp hInput
    (perfectPrismVarpiNativeDividedPowersOfMonic W hW fInv (hMonicInv hf))
    (perfectPrismVarpiNativeDividedPowersOfMonic_base_apply W hW fInv (hMonicInv hf)) n

/-- 概要：元の mod p 入力の実分冪包から任意の分冪標的への射は一意に存在。
方針：標準分冪値を持つ一次関係商の一般普遍性を適用する。
規約：標的は Np の任意の代数と分冪イデアル。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実テンソル比較先の pd 包性。 -/
theorem existsUnique_powerRootPrimeFrobeniusPDMorphismOfMonic
    (hf : f.Monic)
    {B : Type v} [CommRing B] [Algebra Np B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap Np B zp ∈ I) :
    ∃! F : Dp →ₐ[Np] B,
      (powerRootPrimeFrobeniusDividedPowersOfMonic W hW f hf).IsDPMorphism Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism zp
    (powerRootPrimeFrobeniusDividedPowersOfMonic W hW f hf)
    (powerRootPrimeFrobeniusDividedPowersOfMonic_base_apply W hW f hf) Ht hzB

end Prime
end SerrePositivity.BhattScholze.Andre
