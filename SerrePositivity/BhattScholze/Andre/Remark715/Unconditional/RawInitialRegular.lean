module

public import SerrePositivity.BhattScholze.Andre.Remark715.DeltaDivisionUnaryFiniteInitialRegular
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicRawRegular
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# 元の raw 包の最初の有限段の p 正則性

## 概要
BS Rem 7.15（著者版 p.62）の無限根モニック入力について、深さ零の実関係商は p 正則。

## 方針
定数係数が正則な一次多項式の非零因子判定を、元の mod p 関係に適用する。

## 規約
hpR と分母の mod p 正則性は不要。後続有限段と raw 全体の p 正則性はここでは主張しない。

## 使われ方
残る raw p 正則性の有限段帰納法の初期値を無条件に供給する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre

/-- 概要：定数係数が正則な一次多項式は正則。
方針：一つの係数の非零因子性から多項式の非零因子性を得る。
規約：一次係数の正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の初期線形関係の p 飽和性。 -/
theorem unconditionalLinearPolynomial_regular_of_constant
    {R : Type u} [CommRing R] (c b : R) (hb : IsSMulRegular R b) :
    IsSMulRegular (Polynomial R) (Polynomial.C c * Polynomial.X + Polynomial.C b) := by
  have hb' : b ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_iff_left.mpr (fun x hx => hb (hx.trans (mul_zero b).symm))
  have h : Polynomial.C c * Polynomial.X + Polynomial.C b ∈ nonZeroDivisors (Polynomial R) :=
    Polynomial.mem_nonZeroDivisors_of_coeff_mem 0 (by simpa using hb')
  exact (isRegular_iff_mem_nonZeroDivisors.mpr h).left

/-- 概要：指定変数の定数係数正則な一次式は、多変数多項式環でも正則。
方針：指定変数を分離し、残りの変数への平坦拡大で係数正則性を保つ。
規約：変数族の有限性と一次係数の正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の元の自由 δ 環の初期関係。 -/
theorem unconditionalLinearMvPolynomial_regular_of_constant
    {R : Type u} [CommRing R] {τ : Type v} (c b : R) (s : τ) (hb : IsSMulRegular R b) :
    IsSMulRegular (MvPolynomial τ R)
      (MvPolynomial.C c * MvPolynomial.X s + MvPolynomial.C b) := by
  classical
  let e := (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe s).symm).trans
    (MvPolynomial.optionEquivLeft R {t : τ // t ≠ s})
  have he : e (MvPolynomial.C c * MvPolynomial.X s + MvPolynomial.C b) =
      Polynomial.C (MvPolynomial.C c) * Polynomial.X + Polynomial.C (MvPolynomial.C b) := by
    simp [e, MvPolynomial.renameEquiv]
  have hb' := hb.of_flat (S := MvPolynomial {t : τ // t ≠ s} R)
  have hr := unconditionalLinearPolynomial_regular_of_constant
    (MvPolynomial.C c) (MvPolynomial.C b) hb'
  intro x y hxy
  apply e.injective
  apply hr
  simpa only [smul_eq_mul, map_mul, he] using congrArg e hxy

section Initial
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type u} [Unique σ]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L" => RelativeFreeDeltaRing (R := A) σ
local notation "qP" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "qL" => Ideal.Quotient.mk (Ideal.span {(p : L)})
local notation "g" => deltaDivisionIteratedRelation D d a (default : σ) 0
local notation "B" => L ⧸ Ideal.span {g}

/-- 概要：正則な分子の mod p 像だけで、最初の実 δ 関係は mod p で正則。
方針：自由環の実 mod p 同型で定数係数正則な一次式へ移す。
規約：分母の mod p 正則性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の最初の関係商の p 正則性。 -/
theorem unconditionalDeltaDivisionUnaryFirst_mod_prime_regular
    (ha : IsSMulRegular (A ⧸ Ideal.span {(p : A)}) (qP (a default))) :
    IsSMulRegular (L ⧸ Ideal.span {(p : L)}) (qL g) := by
  apply (ringEquiv_isSMulRegular
    (relativeFreeModPrimePolynomialEquiv (p := p) (A := A) (σ := σ)) _).mpr
  rw [relativeFreeModPrimePolynomialEquiv_first]
  have hn : IsSMulRegular (A ⧸ Ideal.span {(p : A)}) (-(qP (a default))) := by
    intro x y hxy
    apply ha
    simpa only [neg_smul, neg_inj] using hxy
  simpa only [map_neg, sub_eq_add_neg] using
    unconditionalLinearMvPolynomial_regular_of_constant (qP d) (-(qP (a default)))
      ((default : σ), 0) hn

/-- 概要：元の最初の関係商は、正則な分子の mod p 像だけで p 正則。
方針：自由源の p 正則性と初期関係の mod p 正則性で順序交換する。
規約：分母の mod p 正則性を追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の無限根モニック有限段の初期値。 -/
theorem unconditionalDeltaDivisionUnaryFirst_prime_regular
    (hpA : IsSMulRegular A (p : A))
    (ha : IsSMulRegular (A ⧸ Ideal.span {(p : A)}) (qP (a default))) :
    IsSMulRegular B (p : B) := by
  have hpL : IsSMulRegular L (p : L) := by
    simpa only [map_natCast] using hpA.of_flat (S := L)
  have h := principal_regular_swap (p : L) g hpL
    (unconditionalDeltaDivisionUnaryFirst_mod_prime_regular D d a ha)
  simpa only [map_natCast] using h
end Initial

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => PowerRootUnaryFreeDeltaRing A p hp
local notation "I" => deltaDivisionFiniteRelationIdeal E dP a

/-- 概要：無限根モニック raw 包の深さ零の実有限関係商は p 正則。
方針：既存のモニック入力の mod p 正則性を初期関係の定数係数判定へ渡す。
規約：hf のみを要求し、hpR と正次数を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の raw p 正則性の有限段帰納法の初期値。 -/
theorem powerRootPrismMonicFinite_prime_regular_zero_of_unconditional (hf : f.Monic) :
    IsSMulRegular (L ⧸ I 0) (p : L ⧸ I 0) := by
  have hpP := powerRootPolynomial_primeRegular p hW.p_mul_injective
  have ha : IsSMulRegular (P ⧸ Ideal.span {(p : P)})
      (Ideal.Quotient.mk (Ideal.span {(p : P)}) (a default)) := by
    simpa only [powerRootPrismMonicUnaryFamily, powerRootMonicPDInput] using
      powerRootPolynomial_monic_mod_prime_regular A p hp f hf
  have h := unconditionalDeltaDivisionUnaryFirst_prime_regular E dP a hpP ha
  let e := Ideal.quotEquivOfEq (deltaDivisionUnaryFiniteIdeal_zero E dP a).symm
  have ht := (ringEquiv_isSMulRegular e (p : _)).mp h
  simpa only [map_natCast] using ht

/-- 概要：無限根モニック入力の最初の mod p 線形関係は、hpR なしに正則。
方針：分子のモニック性から定数係数の正則性を供給する。
規約：任意の変数族を許し、元の非モニック一般形まで無条件化したとはしない。
使われ方：BS Rem 7.15（著者版 p.62）のモニック入力における旧補題の置換先。 -/
theorem powerRootPrismFirstModPrimeRelation_regular_of_monic_unconditional
    (hf : f.Monic) {τ : Type v} (s : τ) :
    IsSMulRegular (MvPolynomial τ (P ⧸ Ideal.span {(p : P)}))
      (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {(p : P)}) dP) * MvPolynomial.X s -
        MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {(p : P)}) (powerRootMonicPDInput p f))) := by
  have ha : IsSMulRegular (P ⧸ Ideal.span {(p : P)})
      (-(Ideal.Quotient.mk (Ideal.span {(p : P)}) (powerRootMonicPDInput p f))) := by
    have hr := powerRootPolynomial_monic_mod_prime_regular A p hp f hf
    intro x y hxy
    apply hr
    simpa only [powerRootMonicPDInput, neg_smul, neg_inj] using hxy
  simpa only [map_neg, sub_eq_add_neg] using
    unconditionalLinearMvPolynomial_regular_of_constant
      (Ideal.Quotient.mk (Ideal.span {(p : P)}) dP)
      (-(Ideal.Quotient.mk (Ideal.span {(p : P)}) (powerRootMonicPDInput p f))) s ha

end SerrePositivity.BhattScholze.Andre
