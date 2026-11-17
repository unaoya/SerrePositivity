module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawPolynomialCoefficients
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientStandardZero
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateCompletedMap
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawPolynomialCoefficients
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateCompletedMap

/-!
# 元の通常形式上の標準 HT 写像の生成元自然性

## 概要
元の標準 HT 写像を、零次形式とその微分で元の係数射と比較する。

## 方針
完備化単位の既存の式と、元の零次類・Bockstein の自然性を使う。

## 規約
選択生成元を厳密に保つ prism 射だけを扱う。

## 使われ方
特定の Zp 係数変更における、元の HT 写像の全次数の照合。
-/

public noncomputable section
universe u
open SerrePositivity.DeRham SerrePositivity.Cosimplicial
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の通常の零次形式の単位は、同じ標準零次 HT 類へ移る。 -/
theorem affineHTRaw_zero (g : Poly (A ⧸ P.ideal) (formVars.{u} r)) :
    (hodgeTateMap P hP r).app 0
      (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} r) p 0
        (formsZeroEquiv (A ⧸ P.ideal) (formVars.{u} r) g)) =
      hodgeTateMapZero P hP r (affineRawPolynomialCoefficient P r g) := by
  rw [← degreeZeroForm_unit_raw P r, (hodgeTateMap P hP r).on_zero]
  simp only [rawCoefficient, affineRawPolynomialCoefficient]

/-- 元の通常の零次形式の微分は、同じ標準零次類の Bockstein へ移る。 -/
theorem affineHTRaw_d_zero (g : Poly (A ⧸ P.ideal) (formVars.{u} r)) :
    (hodgeTateMap P hP r).app 1
      (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} r) p 1
        (deRhamD (A ⧸ P.ideal) (formVars.{u} r) 0
          (formsZeroEquiv (A ⧸ P.ideal) (formVars.{u} r) g))) =
      htBocksteinZero P hP r (affineRawPolynomialCoefficient P r g) := by
  rw [(hodgeTateMap P hP r).on_one]
  have h := etaRaw_d P hP r g
  change hodgeTateMapOne P hP r
    (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} r) p 1
      (deRhamD (A ⧸ P.ideal) (formVars.{u} r) 0
        (formsZeroEquiv (A ⧸ P.ideal) (formVars.{u} r) g))) =
      htBocksteinZero P hP r (rawCoefficient P r g) at h
  simpa only [rawCoefficient, affineRawPolynomialCoefficient] using h

variable {P} {Q : OrientedPrism p B} (f : OrientedPrism.Hom P Q)
variable (hQ : IsBoundedPrism Q) (hg : f.toRingHom P.generator = Q.generator)

/-- 同じ通常零次形式の標準 HT 類は、元の係数変更と可換。 -/
theorem affineHTRaw_zero_natural (g : Poly (A ⧸ P.ideal) (formVars.{u} r)) :
    cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) 0
      ((hodgeTateMap P hP r).app 0
        (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} r) p 0
          (formsZeroEquiv (A ⧸ P.ideal) (formVars.{u} r) g))) =
      (hodgeTateMap Q hQ r).app 0
        (completedFormsUnit (B ⧸ Q.ideal) (formVars.{u} r) p 0
          (formsZeroEquiv (B ⧸ Q.ideal) (formVars.{u} r) (MvPolynomial.map f.quotientMap g))) := by
  rw [affineHTRaw_zero, affineHTRaw_zero, affineHTCoefficient_hodgeTateMapZero,
    affineRawPolynomialCoefficient_natural]

/-- 同じ通常零次形式の微分の標準 HT 類も、元の係数変更と可換。 -/
theorem affineHTRaw_d_zero_natural (g : Poly (A ⧸ P.ideal) (formVars.{u} r)) :
    cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) 1
      ((hodgeTateMap P hP r).app 1
        (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} r) p 1
          (deRhamD (A ⧸ P.ideal) (formVars.{u} r) 0
            (formsZeroEquiv (A ⧸ P.ideal) (formVars.{u} r) g)))) =
      (hodgeTateMap Q hQ r).app 1
        (completedFormsUnit (B ⧸ Q.ideal) (formVars.{u} r) p 1
          (deRhamD (B ⧸ Q.ideal) (formVars.{u} r) 0
            (formsZeroEquiv (B ⧸ Q.ideal) (formVars.{u} r) (MvPolynomial.map f.quotientMap g)))) := by
  rw [affineHTRaw_d_zero, affineHTRaw_d_zero, affineHTCoefficient_htBocksteinZero,
    affineRawPolynomialCoefficient_natural]

end SerrePositivity.BhattScholze.Prismatic
