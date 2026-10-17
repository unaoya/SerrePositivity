module

public import SerrePositivity.BhattScholze.Andre.MonicFamilyFaithfullyFlat

/-!
# André E1・E2：全族の通常関係商と係数商の交換

## 概要

任意多項式族の通常商を係数イデアルでさらに割る操作を、係数変更した多項式族の通常商と同定する。
BS 著者版 Cor 2.39（p.25）、Rem 7.15（p.62）の raw 除算包の実剰余計算に使う。

## 方針

多変数多項式環と係数商の交換同型を関係イデアルの商まで降下する。
代表元の係数写像を明示して、元の係数環商の作用を固定する。

## 規約

モニック性・正次数・族の有限性はこの同型には不要。
通常商の計算であり、導来基底変更との比較は別工程である。

## 使われ方

raw φ/p 包の初期係数商を、mod p のモニック関係の冪商として表示する。
-/

@[expose] public noncomputable section

universe u v

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {R : Type u} [CommRing R] {σ : Type v}
variable (I : Ideal R) (f : σ → Polynomial R)
local notation "IB" => I.map (MvPolynomial.C : R →+* MvPolynomial σ R)
local notation "J" => polynomialFamilyRelationIdeal f
local notation "Jbar" => polynomialFamilyRelationIdeal
  (fun s => Polynomial.map (Ideal.Quotient.mk I) (f s))

/-- 概要：係数商で全族の関係イデアルは係数変更した関係イデアルへ写る。
方針：係数商の可換公式と多項式評価の自然性を生成元に適用する。
規約：元の全族の添字を保持する。
使われ方：BS Cor 2.39（著者版 p.25）の実係数商の同定。 -/
theorem polynomialFamilyIdeal_map_coefficientQuotient :
    ((J).map (Ideal.Quotient.mk IB)).map
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingHom = Jbar := by
  rw [Ideal.map_map, monicPowerFamilyCoefficientQuotient_comp]
  simp only [polynomialFamilyRelationIdeal, Ideal.map_span, ← Set.range_comp']
  congr 1
  congr 1
  funext s
  exact monicRelation_map _ _ _

/-- 概要：係数イデアルと全族の関係を同時に課す商は、係数変更後の全族商と同型。
方針：二重商と多変数係数商の交換同型を合成する。
規約：モニック性を必要としない。
使われ方：BS Rem 7.15（著者版 p.62）の通常剰余環を固定する。 -/
def polynomialFamilyBaseQuotientEquiv :
    (MvPolynomial σ R ⧸ (IB ⊔ J)) ≃+*
      PolynomialFamilyQuotient (fun s => (f s).map (Ideal.Quotient.mk I)) :=
  (DoubleQuot.quotQuotEquivQuotSup IB J).symm.trans
    (Ideal.quotientEquiv _ _
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingEquiv
      (polynomialFamilyIdeal_map_coefficientQuotient I f).symm)

/-- 概要：係数商の同型は任意代表元の係数を商へ写す。
方針：二重商と係数商の代表元公式を使う。
規約：全族の変数は変えない。
使われ方：BS Cor 2.39（著者版 p.25）の元の係数射の追跡。 -/
theorem polynomialFamilyBaseQuotientEquiv_mk (x : MvPolynomial σ R) :
    polynomialFamilyBaseQuotientEquiv I f (Ideal.Quotient.mk (IB ⊔ J) x) =
      Ideal.Quotient.mk Jbar (MvPolynomial.map (Ideal.Quotient.mk I) x) := by
  change Ideal.Quotient.mk Jbar
    ((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm
      (Ideal.Quotient.mk IB x)) = _
  congr 1
  exact DFunLike.congr_fun (monicPowerFamilyCoefficientQuotient_comp σ R I) x

end SerrePositivity.BhattScholze.Andre
