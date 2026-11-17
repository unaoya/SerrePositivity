module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffinePolynomialCoefficients
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.AffineCechPrismBaseChange
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.AffineCechPrismBaseChange
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps

/-!
# affine 包の元の構造切断と係数変更

## 概要
prism の係数変更は、元の完備多項式環から包の剰余への切断を保つ。

## 方針
完備化の普遍性で多項式へ戻し、係数と座標で既存の脚の仕様を使う。

## 規約
両側の包の選択と濃度上限は独立。元の環射と元の切断を比較する。

## 使われ方
Hodge–Tate の零次写像と、次数一の Bockstein 生成元の係数変更。
-/

public noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DerivedCompletion
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) {r n : ℕ} {κ κ' : Cardinal.{u}}
variable (U : AffineEnvelopeTerm P r n κ) (V : AffineEnvelopeTerm Q r n κ')

/-- 元の包の係数変更は、二つの元の基底脚と可換。 -/
theorem affineEnvelopeCoefficientHom_base :
    (affineEnvelopeCoefficientHom f U V).comp U.X.toHom = V.X.toHom.comp f :=
  OrientedPrism.Hom.ext (affineEnvelopeCoefficientMap_spec f U V).2.1

/-- 元の包の係数変更は、完備多項式の標準構造切断を保つ。 -/
theorem affineEnvelopeCoefficientHom_sec :
    (affineEnvelopeCoefficientHom f U V).quotientMap.comp U.X.sec =
      V.X.sec.comp (affinePolynomialCoefficientMap f r) := by
  apply affinePolynomialCoefficient_ext r
    (isModuleComplete_principal_quotient_natCast V.X.B p V.X.Q.generator V.X.Q.complete_p)
  apply MvPolynomial.ringHom_ext'
  · apply RingHom.ext
    intro a
    change (affineEnvelopeCoefficientHom f U V).quotientMap
      (U.X.sec (prismPolynomialUnit P (Fin r) (MvPolynomial.C a))) =
        V.X.sec (affinePolynomialCoefficientMap f r
          (prismPolynomialUnit P (Fin r) (MvPolynomial.C a)))
    rw [affinePolynomialCoefficientMap_unit, MvPolynomial.map_C]
    have hU := RingHom.congr_fun U.X.sec_comp a
    have hV := RingHom.congr_fun V.X.sec_comp (f.quotientMap a)
    change U.X.sec (prismPolynomialUnit P (Fin r) (MvPolynomial.C a)) = _ at hU
    change V.X.sec (prismPolynomialUnit Q (Fin r) (MvPolynomial.C (f.quotientMap a))) = _ at hV
    rw [hU, hV]
    have hb : (affineEnvelopeCoefficientHom f U V).quotientMap.comp U.X.toHom.quotientMap =
        V.X.toHom.quotientMap.comp f.quotientMap := by
      rw [← OrientedPrism.Hom.quotientMap_comp, affineEnvelopeCoefficientHom_base,
        OrientedPrism.Hom.quotientMap_comp]
    exact RingHom.congr_fun hb a
  · intro j
    change (affineEnvelopeCoefficientHom f U V).quotientMap
      (U.X.sec (prismPolynomialUnit P (Fin r) (MvPolynomial.X j))) =
        V.X.sec (affinePolynomialCoefficientMap f r
          (prismPolynomialUnit P (Fin r) (MvPolynomial.X j)))
    rw [U.sec_X, affinePolynomialCoefficientMap_X, V.sec_X]
    exact congrArg (Ideal.Quotient.mk V.X.Q.ideal)
      ((affineEnvelopeCoefficientMap_spec f U V).2.2 j 0)

end SerrePositivity.BhattScholze.Prismatic
