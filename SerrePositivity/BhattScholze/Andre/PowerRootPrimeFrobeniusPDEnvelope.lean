module

public import SerrePositivity.BhattScholze.Andre.PowerRootVarpiPrimeFrobeniusPD
public import SerrePositivity.BhattScholze.Andre.PrincipalDPTransport
public import SerrePositivity.BhattScholze.Andre.PerfectPrismVarpiNativePDEnvelope

/-!
# André E1・E2：元の mod p 入力の実分冪包

## 概要

係数 Frobenius によって元の f の mod p 入力の標準表示へ実分冪構造と pd 普遍性を移す。
BS Rem 7.15(1)（著者版 p.62）の実引戻し比較先の構造。

## 方針

逆係数入力の R/ϖ pd 包と、入力を保つ R/p 係数環同型を使う。

## 規約

prism 商の p 正則性・モニック性を明示し、標的のねじれや完備性は制約しない。

## 使われ方

元の自然な ϖ 剰余の実テンソル底変換の比較先を、実 pd 包として固定する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
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
規約：prism 商の p 正則性とモニック性を明示する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の同定。 -/
def powerRootPrimeFrobeniusDividedPowers
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) (hf : f.Monic) :
    DividedPowers (principalDPPositiveIdeal zp) :=
  principalDPTransportDividedPowers rootEq zv zp hInput
    (perfectPrismVarpiNativeDividedPowers W hW fInv hpR (hMonicInv hf))

/-- 概要：元の入力の n 次分冪は n 次標準生成元。
方針：入力を保つ係数移送の分冪公式と元の標準値を使う。
規約：零次数を含む全次数を扱う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 普遍性の入力。 -/
theorem powerRootPrimeFrobeniusDividedPowers_base_apply
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) (hf : f.Monic) (n : ℕ) :
    (powerRootPrimeFrobeniusDividedPowers W hW f hpR hf).dpow n
      (algebraMap Np Dp zp) = principalDPGenerator zp n :=
  principalDPTransportDividedPowers_base_apply rootEq zv zp hInput
    (perfectPrismVarpiNativeDividedPowers W hW fInv hpR (hMonicInv hf))
    (perfectPrismVarpiNativeDividedPowers_base_apply W hW fInv hpR (hMonicInv hf)) n

/-- 概要：元の mod p 入力の実分冪包から任意の分冪標的への射は一意に存在。
方針：標準分冪値を持つ一次関係商の一般普遍性を適用する。
規約：標的は Np の任意の代数と分冪イデアル。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実テンソル比較先の pd 包性。 -/
theorem existsUnique_powerRootPrimeFrobeniusPDMorphism
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) (hf : f.Monic)
    {B : Type v} [CommRing B] [Algebra Np B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap Np B zp ∈ I) :
    ∃! F : Dp →ₐ[Np] B,
      (powerRootPrimeFrobeniusDividedPowers W hW f hpR hf).IsDPMorphism Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism zp
    (powerRootPrimeFrobeniusDividedPowers W hW f hpR hf)
    (powerRootPrimeFrobeniusDividedPowers_base_apply W hW f hpR hf) Ht hzB

end SerrePositivity.BhattScholze.Andre
