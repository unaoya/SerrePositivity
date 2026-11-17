module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedRawOne
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedCohomology
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawHodgeTateWords
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawFormWords
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawHodgeTateWords
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawPolynomialCoefficients
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateCompletedMap
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawPolynomialCoefficients
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawHodgeTateWords

/-!
# 元の零次・一次HT基底の向きの単位

## 概要
元の多項式・外積基底で、向き付き係数射に現れる一次の単位を明示する。

## 方針
元の形式の係数線形性と座標Bocksteinの単位の式を使う。

## 規約
始域と終域の元の標準HT写像を使い、生成元の単位を一に置き換えない。

## 使われ方
元のηの被覆上の零次・一次の正方形。
-/

@[expose] public noncomputable section
universe u
open SerrePositivity.DeRham SerrePositivity.Cosimplicial
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)

/-- 元の通常形式の多項式作用は、元の標準HT写像の同じ完備係数作用へ移る。 -/
theorem affineHTRawMap_polynomial_smul (i : ℕ)
    (g : Poly (A ⧸ P.ideal) (formVars.{u} r)) (w : forms (A ⧸ P.ideal) (formVars.{u} r) i) :
    letI := htModule P hP r i
    affineHTRawMap P hP r i (g • w) =
      affineRawPolynomialCoefficient P r g • affineHTRawMap P hP r i w := by
  letI := htModule P hP r i
  change (hodgeTateMap P hP r).app i (completedFormsUnit _ _ p i (g • w)) = _
  rw [completedFormsUnit_smul_raw, map_smul]
  rfl

/-- 元の長さ一の座標外積は、同じ座標一次形式の多項式倍。 -/
theorem coordinateFormWord_one_smul (k T : Type u) [CommRing k] [Fintype T] [DecidableEq T]
    (v : Fin 1 → T) (g : Poly k T) :
    coordinateFormWord k T 1 v g = g • dX k T (v 0) := by
  rw [coordinateFormWord, dX, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  congr 1

/-- 元の通常零次形式の標準HT類は、生成元の単位にかかわらず係数射と可換。 -/
theorem affineHTRawMap_zero_any (g : Poly (A ⧸ P.ideal) (formVars.{u} r)) :
    cohomologyMap _ _ (affineHTCoefficientReducedAny f hP hQ r) 0
      (affineHTRawMap P hP r 0 (formsZeroEquiv _ _ g)) =
      affineHTRawMap Q hQ r 0 (formsZeroEquiv _ _ (MvPolynomial.map f.quotientMap g)) := by
  change cohomologyMap _ _ (affineHTCoefficientReducedAny f hP hQ r) 0
    ((hodgeTateMap P hP r).app 0 (completedFormsUnit _ _ p 0 (formsZeroEquiv _ _ g))) =
      (hodgeTateMap Q hQ r).app 0
        (completedFormsUnit _ _ p 0 (formsZeroEquiv _ _ (MvPolynomial.map f.quotientMap g)))
  rw [affineHTRaw_zero, affineHTRaw_zero, affineHTCoefficientAny_hodgeTateMapZero,
    affineRawPolynomialCoefficient_natural]

/-- 元の零次の単項式・外積基底全体で、同じ元の標準HT類を保つ。 -/
theorem affineHTRawMap_basis_zero_any
    (v : (formVars.{u} r →₀ ℕ) × Set.powersetCard (formVars.{u} r) 0) :
    cohomologyMap _ _ (affineHTCoefficientReducedAny f hP hQ r) 0
      (affineHTRawMap P hP r 0 (polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} r) 0 v)) =
      affineHTRawMap Q hQ r 0 (polynomialFormsBasis (B ⧸ Q.ideal) (formVars.{u} r) 0 v) := by
  rw [polynomialFormsBasis_coordinateFormWord, polynomialFormsBasis_coordinateFormWord,
    coordinateFormWord_zero, coordinateFormWord_zero]
  simpa only [MvPolynomial.map_monomial, map_one] using
    affineHTRawMap_zero_any f hP hQ r (MvPolynomial.monomial v.1 1)

variable (v : Bˣ) (hv : f.toRingHom P.generator = Q.generator * (v : B))
include hv
/-- 元の多項式倍の座標一次形式も、同じ向きの単位を係数に持つ。 -/
theorem affineHTRawMap_polynomial_coordinate_unit
    (g : Poly (A ⧸ P.ideal) (formVars.{u} r)) (t : formVars.{u} r) :
    letI := htModule Q hQ r 1
    affineHTRawMap Q hQ r 1 (MvPolynomial.map f.quotientMap g • dX _ _ t) =
      affineBaseToPolynomialMap Q r (v : B) • cohomologyMap _ _
        (affineHTCoefficientReducedAny f hP hQ r) 1
          (affineHTRawMap P hP r 1 (g • dX _ _ t)) := by
  letI := htModule P hP r 1
  letI := htModule Q hQ r 1
  rw [affineHTRawMap_polynomial_smul, affineHTRawMap_coordinate_unit f hP hQ r v hv,
    affineHTRawMap_polynomial_smul, affineHTCoefficientAnyCohomology_smul,
    affineRawPolynomialCoefficient_natural]
  rw [smul_smul, smul_smul, mul_comm]

/-- 元の一次の単項式・外積基底全体で、同じ向きの単位を保持する。 -/
theorem affineHTRawMap_basis_one_unit
    (w : (formVars.{u} r →₀ ℕ) × Set.powersetCard (formVars.{u} r) 1) :
    letI := htModule Q hQ r 1
    affineHTRawMap Q hQ r 1 (polynomialFormsBasis (B ⧸ Q.ideal) (formVars.{u} r) 1 w) =
      affineBaseToPolynomialMap Q r (v : B) • cohomologyMap _ _
        (affineHTCoefficientReducedAny f hP hQ r) 1
          (affineHTRawMap P hP r 1 (polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} r) 1 w)) := by
  letI := htModule Q hQ r 1
  rw [polynomialFormsBasis_coordinateFormWord, polynomialFormsBasis_coordinateFormWord,
    coordinateFormWord_one_smul, coordinateFormWord_one_smul]
  simpa only [MvPolynomial.map_monomial, map_one] using
    affineHTRawMap_polynomial_coordinate_unit f hP hQ r v hv (MvPolynomial.monomial w.1 1)
      (Set.powersetCard.ofFinEmbEquiv.symm w.2 0)

end SerrePositivity.BhattScholze.Prismatic
