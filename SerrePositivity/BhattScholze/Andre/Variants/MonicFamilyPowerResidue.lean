module

public import SerrePositivity.BhattScholze.Andre.MonicFamilySubsetRegular
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# André E1・E2：先行関係の冪と係数商の後のモニック正則性

## 概要

mod p と先行する独立多項式関係の p 乗で割った後も、残りの変数のモニック関係は
非零因子である。BS 著者版 Cor 2.39（p.25）の独立関係族への計算に使う。

## 方針

係数商と多項式環の交換同型を実関係イデアルの商まで降ろす。
多項式評価と冪が可換することから、冪の先行商を任意多項式族の先行商として扱う。

## 規約

p の素数性、先行族のモニック性や有限性はこの正則性には不要。
後続多項式だけモニックとする。prismatic envelope の忠実平坦性は別工程。

## 使われ方

一般モニック族の raw δ p 除算包に一入力を追加する帰納の正則性入力を供給する。
-/

@[expose] public noncomputable section

universe u v

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {R : Type u} [CommRing R] {σ : Type v}
variable (I : Ideal R) (T : Set σ) (f : σ → Polynomial R)

local notation "IB" => I.map (MvPolynomial.C : R →+* MvPolynomial σ R)
local notation "J" => polynomialSubsetRelationIdeal T f
local notation "Jbar" => polynomialSubsetRelationIdeal T
  (fun s => Polynomial.map (Ideal.Quotient.mk I) (f s))

/-- 概要：係数商は先行関係イデアルを係数変更された先行関係イデアルへ送る。
方針：係数商の可換公式と評価の係数変更公式を各生成元に適用する。
規約：任意係数イデアルと任意先行族を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の残余表示の係数を固定する。 -/
theorem polynomialSubsetIdeal_map_coefficientQuotient :
    ((J).map (Ideal.Quotient.mk IB)).map
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingHom = Jbar := by
  rw [Ideal.map_map, monicPowerFamilyCoefficientQuotient_comp]
  simp only [polynomialSubsetRelationIdeal, Ideal.map_span, ← Set.range_comp']
  congr 1
  congr 1
  funext s
  exact monicRelation_map _ _ _

/-- 概要：係数イデアルと先行関係を同時に課す商は、係数変更後の先行関係商に同型。
方針：二重商と係数商の交換同型を合成する。
規約：実商射を保つ同型を選ぶ。
使われ方：BS Cor 2.39（著者版 p.25）の mod p 正則性に適用する。 -/
def polynomialSubsetBaseQuotientEquiv :
    (MvPolynomial σ R ⧸ (IB ⊔ J)) ≃+* (MvPolynomial σ (R ⧸ I) ⧸ Jbar) :=
  (DoubleQuot.quotQuotEquivQuotSup IB J).symm.trans
    (Ideal.quotientEquiv _ _
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingEquiv
      (polynomialSubsetIdeal_map_coefficientQuotient I T f).symm)

/-- 概要：同時商の同型は各代表元の係数をそのまま商へ写す。
方針：二重商と係数商の代表元公式を使う。
規約：関係式の標準像についての計算に用いる。
使われ方：BS Cor 2.39（著者版 p.25）の実残余入力を同定する。 -/
theorem polynomialSubsetBaseQuotientEquiv_mk (x : MvPolynomial σ R) :
    polynomialSubsetBaseQuotientEquiv I T f (Ideal.Quotient.mk (IB ⊔ J) x) =
      Ideal.Quotient.mk Jbar (MvPolynomial.map (Ideal.Quotient.mk I) x) := by
  change Ideal.Quotient.mk Jbar
    ((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm
      (Ideal.Quotient.mk IB x)) = _
  congr 1
  exact DFunLike.congr_fun (monicPowerFamilyCoefficientQuotient_comp σ R I) x

/-- 概要：係数商と先行関係の商の後でも、残りのモニック関係は非零因子。
方針：同時商を係数変更後の商へ移して、先行族商の正則性を適用する。
規約：先行多項式と後続多項式を独立に取る。
使われ方：BS Rem 7.15（著者版 p.62）の独立関係族の正則性入力。 -/
theorem polynomialSubsetBaseQuotient_remaining_isSMulRegular
    (h : Polynomial R) (hh : h.Monic) (s : σ) (hs : s ∉ T) :
    IsSMulRegular (MvPolynomial σ R ⧸ (IB ⊔ J))
      (Ideal.Quotient.mk (IB ⊔ J) (monicRelation h s)) := by
  let e := polynomialSubsetBaseQuotientEquiv I T f
  have he : e (Ideal.Quotient.mk _ (monicRelation h s)) =
      Ideal.Quotient.mk Jbar (monicRelation (h.map (Ideal.Quotient.mk I)) s) := by
    rw [polynomialSubsetBaseQuotientEquiv_mk, monicRelation_map]
  have hr := polynomialSubsetQuotient_remaining_isSMulRegular T
    (fun t => (f t).map (Ideal.Quotient.mk I))
    (h.map (Ideal.Quotient.mk I)) (hh.map (Ideal.Quotient.mk I)) s hs
  intro x y hxy
  apply e.injective
  apply hr
  have heq := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using heq

omit I in
/-- 概要：実 mod p と先行関係の p 乗商の後も残りのモニック関係は非零因子。
方針：先行する冪関係を元の多項式の冪の評価に書き換え、係数商版を適用する。
規約：p の素数性も先行関係の正則性も不要。
使われ方：BS Cor 2.39（著者版 p.25）の raw δ p 除算の有限族帰納に使う。 -/
theorem polynomialSubsetPowerModP_remaining_isSMulRegular
    (p : ℕ) (h : Polynomial R) (hh : h.Monic) (s : σ) (hs : s ∉ T) :
    IsSMulRegular (MvPolynomial σ R ⧸ (Ideal.span {(p : MvPolynomial σ R)} ⊔
      Ideal.span (Set.range fun t : T => monicRelation (f t) (t : σ) ^ p)))
      (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial σ R)} ⊔
        Ideal.span (Set.range fun t : T => monicRelation (f t) (t : σ) ^ p))
          (monicRelation h s)) := by
  have hr := polynomialSubsetBaseQuotient_remaining_isSMulRegular
    (Ideal.span {(p : R)}) T (fun s => (f s) ^ p) h hh s hs
  have hI : (Ideal.span {(p : R)}).map (MvPolynomial.C : R →+* MvPolynomial σ R) =
      Ideal.span {(p : MvPolynomial σ R)} := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton, map_natCast]
  rw [hI] at hr
  have hJ : polynomialSubsetRelationIdeal T (fun s => (f s) ^ p) =
      Ideal.span (Set.range fun t : T => monicRelation (f t) (t : σ) ^ p) := by
    unfold polynomialSubsetRelationIdeal
    congr 1
    congr 1
    funext t
    exact Polynomial.eval₂_pow _ _ p
  rw [hJ] at hr
  exact hr

end SerrePositivity.BhattScholze.Andre
