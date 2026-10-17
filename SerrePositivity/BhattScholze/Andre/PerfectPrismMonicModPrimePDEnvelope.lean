module

public import SerrePositivity.BhattScholze.Andre.MonicModPrimePDEnvelope
public import SerrePositivity.BhattScholze.Andre.PrincipalDPTruncatedPresentation

/-!
# André E1・E2：完全 prism 上のモニック入力の実 mod p 分冪包

## 概要

完全 prism の係数環上のモニック関係に対して、mod p 実分冪構造と普遍性を得る。
その台環は入力の p 乗商上の可算切断多項式商であり、係数商上自由。
BS Rem 7.15(1)（著者版 p.62）の完全 prism 上のモニック入力の計算。

## 方針

完全性から p 正則性、p 完備性と Jacobson 根基から p 局所性を供給する。
台環の表示には一次関係商の既存の切断同型を用いる。

## 規約

このファイルの変数は通常多項式変数である。無限 p 冪根変数への移行と
prismatic envelope の Frobenius 引戻しとの比較は別工程。

## 使われ方

原典の実 pd 包の明示表示と、prismatic envelope の剰余の同定を接続する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]

/-- 概要：完全 prism の係数環は p 局所。
方針：p 完備性から p の Jacobson 根基への所属を得て、Bezout の単元補題を使う。
規約：完備性の仮定は追加せず完全 prism から供給する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の階乗計算の実入力。 -/
theorem perfectPrism_primeLocal (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) :
    ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A) := by
  let := P.isAdicComplete_p_of_perfect hP
  exact primeLocal_of_prime_mem_jacobson
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)}) (Ideal.mem_span_singleton_self _))

local notation "B" => MvPolynomial σ A
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : B)})
local notation "Q" => B ⧸ Ideal.span {(p : B)}

/-- 概要：完全 prism 上のモニック入力の mod p 表示環には実分冪構造がある。
方針：p 正則性と p 局所性を完全 prism から供給し、モニック入力の構造を適用する。
規約：補助的な持ち上げの正則性を仮定として残さない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の完全 prism 上の実 pd 包。 -/
def perfectPrismMonicModPrimeDividedPowers
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (s : σ) :
    DividedPowers (principalDPPositiveIdeal (bar (monicRelation f s))) :=
  monicModPrimePDDividedPowers (perfectPrism_primeLocal P hP) hP.p_mul_injective
    P.deltaStructure f hf s

/-- 概要：完全 prism 上のモニック入力の実 mod p 分冪包の普遍射は一意に存在する。
方針：持ち上げの各入力を完全 prism とモニック性から内部で供給する。
規約：標的のねじれ・正則性・δ 構造・完備性は仮定しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）のモニック入力の実 pd 普遍性。 -/
theorem existsUnique_perfectPrismMonicModPrimePDMorphism
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (s : σ)
    {T : Type v} [CommRing T] [Algebra Q T] {I : Ideal T} (Ht : DividedPowers I)
    (hyT : algebraMap Q T (bar (monicRelation f s)) ∈ I) :
    ∃! F : MonicModPrimePDEnvelope (p := p) f s →ₐ[Q] T,
      (perfectPrismMonicModPrimeDividedPowers P hP f hf s).IsDPMorphism Ht F.toRingHom :=
  existsUnique_monicModPrimePDMorphism (perfectPrism_primeLocal P hP) hP.p_mul_injective
    P.deltaStructure f hf s Ht hyT

omit [Fact p.Prime] in
/-- 概要：実 mod p 多項式係数商では p は零。
方針：p が定義の主イデアルに属することを使う。
規約：係数環の標数自体には条件を置かない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の正標数の切断表示への入力。 -/
theorem monicModPrimeCoefficient_prime_eq_zero : (p : Q) = 0 := by
  change Ideal.Quotient.mk (Ideal.span {(p : B)}) (p : B) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- 概要：モニック入力の mod p 分冪包の台環は入力の p 乗商上の可算切断表示。
方針：同じ一次関係商の係数商上の具体的同型を使う。
規約：台環の同型自体にはモニック性や prism は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の明示表示。 -/
def monicModPrimePDEnvelope_truncatedEquiv (f : Polynomial A) (s : σ) :
    letI := principalDPQuotientAlgebra (Fact.out : p.Prime).pos
      (monicModPrimeCoefficient_prime_eq_zero (σ := σ) (A := A) (p := p))
      (bar (monicRelation f s))
    MonicModPrimePDEnvelope (p := p) f s ≃ₐ[Q ⧸ Ideal.span {(bar (monicRelation f s)) ^ p}]
      PrincipalDPTruncatedPresentation p (bar (monicRelation f s)) :=
  principalDPTruncatedQuotientAlgEquiv p monicModPrimeCoefficient_prime_eq_zero _

/-- 概要：モニック入力の実 mod p 分冪包の台環は入力の p 乗係数商上自由。
方針：明示切断表示を介した自由性を同じ係数商作用に適用する。
規約：分冪構造の存在にはモニック性を使うが、この台加群の自由性には不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の pd 包の自由性。 -/
theorem monicModPrimePDEnvelope_quotient_free (f : Polynomial A) (s : σ) :
    letI := principalDPQuotientAlgebra (Fact.out : p.Prime).pos
      (monicModPrimeCoefficient_prime_eq_zero (σ := σ) (A := A) (p := p))
      (bar (monicRelation f s))
    Module.Free (Q ⧸ Ideal.span {(bar (monicRelation f s)) ^ p})
      (MonicModPrimePDEnvelope (p := p) f s) :=
  principalDPPresentation_free_via_truncated p monicModPrimeCoefficient_prime_eq_zero _

end SerrePositivity.BhattScholze.Andre
