module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismVarpiPDComparison
public import SerrePositivity.BhattScholze.Andre.PrincipalDPPositiveUniversal

/-!
# André E1・E2：原典の R/ϖ 無限根環上の実 pd 包

## 概要

p 正則な prism 商の場合、R/ϖ 上の無限根環のモニック入力の標準表示に、
実分冪構造と任意の分冪標的への普遍性を与える。
BS Rem 7.15(1)（著者版 p.62）の pd 包の係数環を原典通りにする。

## 方針

x=φ⁻¹(d) の係数像で還元した実分冪構造を、検証済みの表示環同型で移送する。
入力元の標準分冪値を移し、一次関係商の一般の実普遍性を使う。

## 規約

prism 商の p 正則性を明示し、標的のねじれ・完備性には条件を課さない。

## 使われ方

原典の pd 包の切断表示と自由性を、同じ実分冪構造・台環に対して述べるための入口。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
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
方針：還元済みの構造を正次数イデアルを保つ表示環同型で移す。
規約：prism 商の p 正則性を明示する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の構造。 -/
def perfectPrismVarpiNativeDividedPowers
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) (hf : f.Monic) :
    DividedPowers (principalDPPositiveIdeal zv) :=
  DividedPowers.ofRingEquiv (perfectPrismVarpiPDEnvelopeEquiv_positiveIdeal W hW f)
    (perfectPrismVarpiPowerRootDividedPowers W hW hpR f hf)

/-- 概要：原典の係数環上でも入力元の分冪は全標準生成元に一致する。
方針：移送公式と還元前の標準値の公式、同型の入力・生成元の比較を使う。
規約：全次数 n を含む。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 普遍性への入力。 -/
theorem perfectPrismVarpiNativeDividedPowers_base_apply
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) (hf : f.Monic) (n : ℕ) :
    (perfectPrismVarpiNativeDividedPowers W hW f hpR hf).dpow n
      (algebraMap Nv Dv zv) = principalDPGenerator zv n := by
  rw [← perfectPrismVarpiPDEnvelopeEquiv_input W hW f,
    perfectPrismVarpiNativeDividedPowers, DividedPowers.ofRingEquiv_dpow_apply,
    perfectPrismVarpiPowerRootDividedPowers_base_apply,
    perfectPrismVarpiPDEnvelopeEquiv_generator]

/-- 概要：原典の係数環上の実 pd 包から任意の分冪標的への射は一意に存在する。
方針：移送済みの実分冪構造と標準値を一般の pd 普遍性へ供給する。
規約：標的は無限根環 Nv の任意の代数。
使われ方：BS Rem 7.15(1)（著者版 p.62）のモニック入力の実 pd 包の同定。 -/
theorem existsUnique_perfectPrismVarpiNativePDMorphism
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) (hf : f.Monic)
    {B : Type v} [CommRing B] [Algebra Nv B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap Nv B zv ∈ I) :
    ∃! F : Dv →ₐ[Nv] B,
      (perfectPrismVarpiNativeDividedPowers W hW f hpR hf).IsDPMorphism Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism zv
    (perfectPrismVarpiNativeDividedPowers W hW f hpR hf)
    (perfectPrismVarpiNativeDividedPowers_base_apply W hW f hpR hf) Ht hzB

end SerrePositivity.BhattScholze.Andre
