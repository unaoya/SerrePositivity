module

public import SerrePositivity.BhattScholze.Andre.Remark715.RegularPrincipalModPrimeUniversal
public import SerrePositivity.BhattScholze.Andre.MonicRelationResidue
public import SerrePositivity.BhattScholze.Delta.Free.PolynomialRankOneDelta
public import SerrePositivity.BhattScholze.Prism.Basic.PerfectOrientedPrism

/-!
# André E1・E2：モニック入力の実 mod p 分冪包

## 概要

p 正則・p 局所 δ 係数環上のモニック多項式を独立変数で評価した入力に対し、
mod p 一次関係商の実分冪構造と普遍性を構成する。
BS Rem 7.15(1)（著者版 p.62）のモニック入力への適用。

## 方針

多項式環の自由性から p 正則性、モニック性から mod p 正則性を供給し、
正則持ち上げの実分冪構造と普遍性を適用する。

## 規約

多項式環の mod p 商をそのまま使う。無限 p 冪根変数や prismatic Frobenius 引戻しの
比較をこのファイルだけで主張しない。

## 使われ方

完全 prism 上の入力から、実 pd 包の表示と通常の忠実平坦性へ接続する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type u}

/-- 概要：p が Jacobson 根基に属すれば p と互いに素な自然数は単元。
方針：Bezout 等式の p 項を Jacobson 根基へ移し、残りの積の単元性を得る。
規約：係数環の非零性を要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の完全 prism から p 局所性を供給する。 -/
theorem primeLocal_of_prime_mem_jacobson (hJac : (p : A) ∈ Ideal.jacobson (⊥ : Ideal A)) :
    ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A) := by
  intro m hm
  obtain ⟨a, b, hab⟩ := (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr hm).cast
    (R := A)
  have hunit : IsUnit (b * (m : A)) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    have he : b * (m : A) - 1 = -(a * (p : A)) := by
      rw [← hab]
      ring
    rw [he]
    exact (Ideal.jacobson (⊥ : Ideal A)).neg_mem
      ((Ideal.jacobson (⊥ : Ideal A)).mul_mem_left a hJac)
  exact isUnit_of_mul_isUnit_right hunit

omit [Fact p.Prime] in
/-- 概要：係数環で p が正則なら多変数多項式環でも正則。
方針：多項式環の自由性による平坦性で正則性を移す。
規約：変数族の有限性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の正則持ち上げの入力。 -/
theorem monicPolynomialRing_primeRegular
    (hpA : Function.Injective (fun a : A => (p : A) * a)) :
    Function.Injective (fun a : MvPolynomial σ A => (p : MvPolynomial σ A) * a) := by
  simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
    (show IsSMulRegular A (p : A) from hpA).of_flat (S := MvPolynomial σ A)

omit [Fact p.Prime] in
/-- 概要：p 局所な係数環上の多項式環も p 局所。
方針：自然数の単元を係数射で送る。
規約：多項式の単元全体の分類は使わない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の階乗計算の入力。 -/
theorem monicPolynomialRing_primeLocal
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) :
    ∀ m : ℕ, ¬p ∣ m → IsUnit (m : MvPolynomial σ A) := by
  intro m hm
  simpa only [map_natCast] using (hlocal m hm).map (MvPolynomial.C : A →+* MvPolynomial σ A)

local notation "B" => MvPolynomial σ A
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : B)})
local notation "Q" => B ⧸ Ideal.span {(p : B)}

/-- 概要：モニック関係の mod p 一次関係商の台環。
方針：モニック多項式の指定変数での評価を実 mod p 商に送り、分冪表示環を取る。
規約：この台環の定義にはモニック性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の候補。 -/
abbrev MonicModPrimePDEnvelope (f : Polynomial A) (s : σ) :=
  PrincipalDPPresentation Q (bar (monicRelation f s))

/-- 概要：モニック入力の mod p 表示環の正次数イデアルに実分冪構造がある。
方針：多項式環の p 正則性・p 局所性とモニック関係の mod p 正則性を内部で供給する。
規約：係数環の p 正則性・p 局所性と δ 構造は明示する。正次数は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）のモニック入力の実 pd 包。 -/
def monicModPrimePDDividedPowers
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (f : Polynomial A) (hf : f.Monic) (s : σ) :
    DividedPowers (principalDPPositiveIdeal (bar (monicRelation f s))) :=
  regularPrincipalModPrimeDividedPowers (monicPolynomialRing_primeLocal hlocal)
    (monicPolynomialRing_primeRegular hpA) (polynomialRankOneDeltaStructure σ D)
    (monicRelation f s) (monicRelation_modP_isSMulRegular p f hf s)

/-- 概要：モニック入力の実分冪構造では入力元の n 次分冪が標準生成元に一致。
方針：正則入力の評価公式へ具体的なモニック入力を代入する。
規約：n=0 を含める。
使われ方：BS Rem 7.15(1)（著者版 p.62）の普遍性と明示表示の照合。 -/
theorem monicModPrimePDDividedPowers_base_apply
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (f : Polynomial A) (hf : f.Monic) (s : σ) (n : ℕ) :
    (monicModPrimePDDividedPowers hlocal hpA D f hf s).dpow n
      (algebraMap Q _ (bar (monicRelation f s))) =
      principalDPGenerator (bar (monicRelation f s)) n :=
  regularPrincipalModPrimeDividedPowers_base_apply (monicPolynomialRing_primeLocal hlocal)
    (monicPolynomialRing_primeRegular hpA) (polynomialRankOneDeltaStructure σ D)
    (monicRelation f s) (monicRelation_modP_isSMulRegular p f hf s) n

/-- 概要：モニック入力の実 mod p 分冪包から任意の分冪標的への射は一意に存在する。
方針：構成した実分冪構造と標準生成元公式を一次関係商の普遍性へ渡す。
規約：標的の p ねじれ・正則性・δ 構造・完備性には条件を置かない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包のモニック入力への適用。 -/
theorem existsUnique_monicModPrimePDMorphism
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (f : Polynomial A) (hf : f.Monic) (s : σ)
    {T : Type v} [CommRing T] [Algebra Q T] {I : Ideal T} (Ht : DividedPowers I)
    (hyT : algebraMap Q T (bar (monicRelation f s)) ∈ I) :
    ∃! F : MonicModPrimePDEnvelope (p := p) f s →ₐ[Q] T,
      (monicModPrimePDDividedPowers hlocal hpA D f hf s).IsDPMorphism Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism _ (monicModPrimePDDividedPowers hlocal hpA D f hf s)
    (monicModPrimePDDividedPowers_base_apply hlocal hpA D f hf s) Ht hyT

end SerrePositivity.BhattScholze.Andre
