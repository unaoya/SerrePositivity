module

public import SerrePositivity.BhattScholze.Andre.MonicRelation
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.MonicPowerFamilyBaseQuotient

/-!
# André E1：係数商後のモニック関係の正則性

## 概要

任意の係数イデアルで割った後も、指定変数のモニック関係式は非零因子である。
BS 著者版 Cor 2.39（p.25）、Rem 7.15(1)（p.62）の正則性入力を供給する。

## 方針

係数商と多項式環の交換同型で元の商を移し、モニック性の係数変更と変数分離を使う。
既存の冪根族のファイルから使うのは任意多項式上の係数射の恒等式だけである。

## 規約

係数環・係数イデアルは任意で、正次数や δ 構造を要求しない。
実導来還元の離散性や prismatic envelope の比較は別工程である。

## 使われ方

任意モニック f を入力する一元 raw δ p 除算の p 正則性の前提に用いる。
-/

@[expose] public noncomputable section

universe u v w

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：モニック関係式の評価は係数変更と可換である。
方針：多項式評価の環射に関する自然性を使う。
規約：モニック性自体はこの恒等式には不要である。
使われ方：BS Rem 7.15（著者版 p.62）の残余関係式を同定する。 -/
theorem monicRelation_map {R : Type u} {B : Type w} [CommRing R] [CommRing B]
    {σ : Type v} (φ : R →+* B) (f : Polynomial R) (s : σ) :
    MvPolynomial.map φ (monicRelation f s) = monicRelation (f.map φ) s := by
  unfold monicRelation
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, MvPolynomial.map_X]
  congr 1
  ext a
  simp

/-- 概要：係数商に沿う拡張イデアルで割っても、モニック関係式の像は非零因子。
方針：多変数多項式環と係数商の交換同型を通じて既知の正則性へ帰着する。
規約：零環と任意イデアルを許す。
使われ方：BS Cor 2.39（著者版 p.25）の mod p 正則性をモニック性から供給する。 -/
theorem monicRelation_coefficientQuotient_isSMulRegular
    {R : Type u} [CommRing R] {σ : Type v}
    (I : Ideal R) (f : Polynomial R) (hf : f.Monic) (s : σ) :
    IsSMulRegular (MvPolynomial σ R ⧸ I.map MvPolynomial.C)
      (Ideal.Quotient.mk (I.map MvPolynomial.C) (monicRelation f s)) := by
  let e := (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm
  have he : e (Ideal.Quotient.mk (I.map MvPolynomial.C) (monicRelation f s)) =
      monicRelation (f.map (Ideal.Quotient.mk I)) s := by
    rw [← monicRelation_map]
    exact DFunLike.congr_fun (monicPowerFamilyCoefficientQuotient_comp σ R I) _
  have h := monicRelation_isSMulRegular (f.map (Ideal.Quotient.mk I))
    (hf.map (Ideal.Quotient.mk I)) s
  intro x y hxy
  apply e.injective
  apply h
  have hh := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using hh

/-- 概要：モニック関係式は実際の p 主イデアル商でも非零因子。
方針：係数の p 主イデアルの多項式環への像を照合する。
規約：p の素数性・係数環の p 正則性は不要。
使われ方：BS Cor 2.39（著者版 p.25）の raw δ 除算の正則性入力。 -/
theorem monicRelation_modP_isSMulRegular
    {R : Type u} [CommRing R] {σ : Type v}
    (p : ℕ) (f : Polynomial R) (hf : f.Monic) (s : σ) :
    IsSMulRegular (MvPolynomial σ R ⧸ Ideal.span {(p : MvPolynomial σ R)})
      (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial σ R)}) (monicRelation f s)) := by
  have h := monicRelation_coefficientQuotient_isSMulRegular (Ideal.span {(p : R)}) f hf s
  have hI : (Ideal.span {(p : R)}).map (MvPolynomial.C : R →+* MvPolynomial σ R) =
      Ideal.span {(p : MvPolynomial σ R)} := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton, map_natCast]
  rw [hI] at h
  exact h

end SerrePositivity.BhattScholze.Andre
