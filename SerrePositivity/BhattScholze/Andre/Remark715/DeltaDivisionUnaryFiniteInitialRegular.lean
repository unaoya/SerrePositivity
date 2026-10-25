module

public import SerrePositivity.BhattScholze.Andre.Remark715.DeltaDivisionFinitePrimeQuotients
public import SerrePositivity.CommutativeAlgebra.FlatRegularQuotient

/-!
# André E1・E2：最初の一元 raw 関係商の p,d 正則性

## 概要

係数環で p が正則、mod p で d が正則、mod(p,d) で分子が正則なら、
最初の線形除算関係を課した有限段でも p と mod p の d は正則。
BS Rem 7.15（著者版 p.62）の有限段帰納法の初期値。

## 方針

mod p の自由多項式環へ係数変更し、正則な線形関係とその係数の正則性を使う。

## 規約

δ(d) の単元性は初期段には不要。完備化全体の正則性は別工程。

## 使われ方

無限根モニック入力の正則対を全有限 δ 関係商へ渡す。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "qp" => Ideal.Quotient.mk (Ideal.span {(p : L₀)})

/-- 概要：自由 δ 環の mod p は mod p 係数上の同じ自由多項式環。
方針：標準の多項式係数商同型で自然数の像を照合する。
規約：δ 構造を係数商に入れない通常環同型。
使われ方：BS Rem 7.15（著者版 p.62）の最初の線形関係の計算。 -/
def relativeFreeModPrimePolynomialEquiv :
    (L₀ ⧸ Ideal.span {(p : L₀)}) ≃+* MvPolynomial (σ × ℕ) R₀ :=
  (Ideal.quotEquivOfEq (show Ideal.span {(p : L₀)} =
    (Ideal.span {(p : A)}).map (MvPolynomial.C : A →+* L₀) by
      rw [Ideal.map_span, Set.image_singleton, map_natCast])).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial
      (σ := σ × ℕ) (Ideal.span {(p : A)})).symm.toRingEquiv

omit [Fact p.Prime] in
/-- 概要：自由環の mod p 同型は各多項式の係数だけを還元する。
方針：標準多項式商比較の合成公式を使う。
規約：全ての自由環元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の係数・初期関係の照合。 -/
theorem relativeFreeModPrimePolynomialEquiv_mk (t : L₀) :
    relativeFreeModPrimePolynomialEquiv (p := p) (A := A) (σ := σ) (qp t) =
      MvPolynomial.map bar t := by
  rw [relativeFreeModPrimePolynomialEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact RingHom.congr_fun (monicPowerFamilyCoefficientQuotient_comp (σ × ℕ) A
    (Ideal.span {(p : A)})) t

/-- 概要：最初の δ 関係の mod p 像は還元した係数による同じ線形関係。
方針：δ 反復の深さ零の定義と係数変更公式を使う。
規約：添字 s の初期変数を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の初期有限段の正則性。 -/
theorem relativeFreeModPrimePolynomialEquiv_first (s : σ) :
    relativeFreeModPrimePolynomialEquiv (p := p) (A := A) (σ := σ)
      (qp (deltaDivisionIteratedRelation D d a s 0)) =
        MvPolynomial.C (bar d) * MvPolynomial.X (s, 0) - MvPolynomial.C (bar (a s)) := by
  rw [relativeFreeModPrimePolynomialEquiv_mk]
  change MvPolynomial.map bar (MvPolynomial.C d * MvPolynomial.X (s, 0) -
    MvPolynomial.C (a s)) = _
  rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

variable [Unique σ]
local notation "g" => deltaDivisionIteratedRelation D d a (default : σ) 0
local notation "B" => L₀ ⧸ Ideal.span {g}
local notation "qg" => Ideal.Quotient.mk (Ideal.span {g})
local notation "G" => MvPolynomial.C (bar d) * MvPolynomial.X ((default : σ), 0) -
  MvPolynomial.C (bar (a default))
local notation "F" => relativeFreeModPrimePolynomialEquiv (p := p) (A := A) (σ := σ)

/-- 概要：最初の関係商の mod p は還元係数上の線形関係商と環同型。
方針：二重商を交換し、自由環の mod p 同型を線形関係の商へ降ろす。
規約：最初の実 δ 関係だけを課す。
使われ方：BS Rem 7.15（著者版 p.62）の最初の商での d 正則性。 -/
def deltaDivisionUnaryFirstPrimeEquiv :
    (B ⧸ Ideal.span {(p : B)}) ≃+* (MvPolynomial (σ × ℕ) R₀ ⧸ Ideal.span {G}) :=
  ((Ideal.quotEquivOfEq (show Ideal.span {(p : B)} = Ideal.span {qg (p : L₀)} by
    rw [map_natCast])).trans (principalDoubleQuotSwapEquiv g (p : L₀))).trans
    (Ideal.quotientEquiv _ _ F (by
      rw [Ideal.map_span, Set.image_singleton]
      congr 1
      congr 1
      exact (relativeFreeModPrimePolynomialEquiv_first D d a default).symm))

/-- 概要：最初の関係の mod p 比較は元の係数を還元した係数へ送る。
方針：二重商交換と自由環の mod p の代表元公式を使う。
規約：元の A の全係数を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の初期係数正則性の移送。 -/
theorem deltaDivisionUnaryFirstPrimeEquiv_coeff (r : A) :
    deltaDivisionUnaryFirstPrimeEquiv D d a
      (Ideal.Quotient.mk _ (qg (MvPolynomial.C r))) =
        Ideal.Quotient.mk (Ideal.span {G}) (MvPolynomial.C (bar r)) := by
  rw [deltaDivisionUnaryFirstPrimeEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, principalDoubleQuotSwapEquiv_mk, Ideal.quotientEquiv_mk,
    relativeFreeModPrimePolynomialEquiv_mk, MvPolynomial.map_C]

/-- 概要：最初の実線形 δ 関係は mod p の自由環上で正則。
方針：係数 d の正則性から一次式の正則性を得て戻す。
規約：分子の正則性はこの非零因子判定には不要。
使われ方：BS Rem 7.15（著者版 p.62）の初期関係商の p 正則性。 -/
theorem deltaDivisionUnaryFirst_mod_prime_regular
    (hdA : IsSMulRegular R₀ (bar d)) :
    IsSMulRegular (L₀ ⧸ Ideal.span {(p : L₀)}) (qp g) := by
  apply (ringEquiv_isSMulRegular F _).mpr
  rw [relativeFreeModPrimePolynomialEquiv_first]
  simpa only [map_neg, sub_eq_add_neg] using
    linearMvPolynomial_regular (bar d) (-(bar (a default))) ((default : σ), 0) hdA

/-- 概要：最初の一元有限 δ 関係商は p 正則で、その mod p で d も正則。
方針：p と初期関係の順序交換、還元係数上の線形関係商の係数正則性を使う。
規約：係数環の正則対と分子の mod(p,d) 正則性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の全有限段の同時帰納法の初期値。 -/
theorem deltaDivisionUnaryFirst_regular
    (hpA : IsSMulRegular A (p : A))
    (hdA : IsSMulRegular R₀ (bar d))
    (haA : IsSMulRegular (R₀ ⧸ Ideal.span {bar d})
      (Ideal.Quotient.mk (Ideal.span {bar d}) (bar (a default)))) :
    IsSMulRegular B (p : B) ∧
      IsSMulRegular (B ⧸ Ideal.span {(p : B)})
        (Ideal.Quotient.mk (Ideal.span {(p : B)}) (qg (MvPolynomial.C d))) := by
  refine ⟨?_, ?_⟩
  · have hpL : IsSMulRegular L₀ (p : L₀) := by
      simpa only [map_natCast] using hpA.of_flat (S := L₀)
    have h := principal_regular_swap (p : L₀) g hpL
      (deltaDivisionUnaryFirst_mod_prime_regular D d a hdA)
    simpa only [map_natCast] using h
  · let e := deltaDivisionUnaryFirstPrimeEquiv D d a
    apply (ringEquiv_isSMulRegular e _).mpr
    rw [deltaDivisionUnaryFirstPrimeEquiv_coeff]
    exact linearMvPolynomial_coefficient_regular_quotient (bar d) (bar (a default))
      ((default : σ), 0) hdA haA

end SerrePositivity.BhattScholze.Andre
