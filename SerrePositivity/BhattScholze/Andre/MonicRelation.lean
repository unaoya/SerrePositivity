module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Logic.Equiv.Option
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# André E1：独立変数のモニック関係式

## 概要

任意のモニック多項式を多変数多項式環の指定変数で評価すると非零因子になる。
BS 著者版 Rem 7.15(1)（p.62）の pd 包の計算に必要な正則性の通常代数部分である。

## 方針

指定変数を一変数多項式として分離し、係数変更されたモニック多項式の正則性を移送する。
既存の冪根関係式の場合と同じ証明を任意のモニック多項式へ一般化する。

## 規約

係数環は任意で零環も許す。この正則性だけには正次数は不要である。
pd 包との比較や完備化後の忠実平坦性は主張しない。

## 使われ方

一元のモニック関係式と、独立変数の有限族を扱う際の最初の正則性入力に使う。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：指定変数に課す通常の多項式関係式。
方針：係数を定数多項式へ写して評価する。
規約：δ 構造を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の一元関係の多変数版。 -/
def monicRelation {R : Type u} [CommRing R] {σ : Type v}
    (f : Polynomial R) (s : σ) : MvPolynomial σ R :=
  f.eval₂ MvPolynomial.C (MvPolynomial.X s)

/-- 概要：指定変数のモニック関係式は多変数多項式環で非零因子。
方針：指定変数の分離同型でモニックの一変数多項式に移す。
規約：正次数・素数・δ 構造を仮定しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の pd 包の正則性入力。 -/
theorem monicRelation_isSMulRegular {R : Type u} [CommRing R] {σ : Type v}
    (f : Polynomial R) (hf : f.Monic) (s : σ) :
    IsSMulRegular (MvPolynomial σ R) (monicRelation f s) := by
  classical
  let e := (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe s).symm).trans
    (MvPolynomial.optionEquivLeft R {t : σ // t ≠ s})
  have he : e (monicRelation f s) =
      f.map (MvPolynomial.C : R →+* MvPolynomial {t : σ // t ≠ s} R) := by
    change e.toRingHom (f.eval₂ MvPolynomial.C (MvPolynomial.X s)) = _
    rw [Polynomial.hom_eval₂]
    have hc : e.toRingHom.comp MvPolynomial.C =
        Polynomial.C.comp (MvPolynomial.C : R →+* MvPolynomial {t : σ // t ≠ s} R) := by
      ext a
      simp [e, MvPolynomial.renameEquiv]
    rw [hc]
    have hx : e.toRingHom (MvPolynomial.X s) = Polynomial.X := by
      simp [e, MvPolynomial.renameEquiv]
    rw [hx]
    rfl
  have h := (hf.map (MvPolynomial.C : R →+* MvPolynomial {t : σ // t ≠ s} R)).isRegular.left
  intro x y hxy
  apply e.injective
  apply h
  have hh := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using hh

end SerrePositivity.BhattScholze.Andre
