module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedStandardZero
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawHodgeTateWords

/-!
# 元の座標一次 HT 類の向きの単位

## 概要
元の通常形式の微分と座標一次形式について、係数変更に現れる単位を明示する。

## 方針
元の標準 HT 写像の生成元上の値を、単位付き Bockstein の自然性へ戻す。

## 規約
同じ完備化単位と同じ標準 HT 写像を使う。向きの単位を一と仮定しない。

## 使われ方
Construction 6.1 の被覆で元の affine line の一次の標準写像を照合する。
-/

public noncomputable section
universe u
open SerrePositivity.DeRham SerrePositivity.Cosimplicial
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)
variable (v : Bˣ) (hv : f.toRingHom P.generator = Q.generator * (v : B))

include hv
/-- 元の座標一次形式の像の比較は、元の向きの単位 v を係数に持つ。 -/
theorem affineHTRawMap_coordinate_unit (t : formVars.{u} r) :
    letI := htModule Q hQ r 1
    affineHTRawMap Q hQ r 1 (dX (B ⧸ Q.ideal) (formVars.{u} r) t) =
      affineBaseToPolynomialMap Q r (v : B) •
        cohomologyMap _ _ (affineHTCoefficientReducedAny f hP hQ r) 1
          (affineHTRawMap P hP r 1 (dX (A ⧸ P.ideal) (formVars.{u} r) t)) := by
  letI := htModule Q hQ r 1
  rw [affineHTRawMap_coordinate, affineHTRawMap_coordinate]
  have h := affineHTCoefficientAny_htBocksteinZero_unit f hP hQ r v hv
    (prismPolynomialUnit P (Fin r) (MvPolynomial.X t.down))
  rwa [affinePolynomialCoefficientMap_X] at h

/-- 元の通常零次形式の微分の比較も、同じ向きの単位 v を係数に持つ。 -/
theorem affineHTRaw_d_zero_unit (g : Poly (A ⧸ P.ideal) (formVars.{u} r)) :
    letI := htModule Q hQ r 1
    (hodgeTateMap Q hQ r).app 1
        (completedFormsUnit (B ⧸ Q.ideal) (formVars.{u} r) p 1
          (deRhamD (B ⧸ Q.ideal) (formVars.{u} r) 0
            (formsZeroEquiv (B ⧸ Q.ideal) (formVars.{u} r) (MvPolynomial.map f.quotientMap g)))) =
      affineBaseToPolynomialMap Q r (v : B) •
        cohomologyMap _ _ (affineHTCoefficientReducedAny f hP hQ r) 1
          ((hodgeTateMap P hP r).app 1
            (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} r) p 1
              (deRhamD (A ⧸ P.ideal) (formVars.{u} r) 0
                (formsZeroEquiv (A ⧸ P.ideal) (formVars.{u} r) g)))) := by
  letI := htModule Q hQ r 1
  rw [affineHTRaw_d_zero, affineHTRaw_d_zero, ← affineRawPolynomialCoefficient_natural]
  exact affineHTCoefficientAny_htBocksteinZero_unit f hP hQ r v hv _

end SerrePositivity.BhattScholze.Prismatic
