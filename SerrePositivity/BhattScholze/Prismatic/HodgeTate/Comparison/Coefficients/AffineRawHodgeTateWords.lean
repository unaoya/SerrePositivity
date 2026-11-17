module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawHodgeTateGenerators
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawFormWords
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateOneGenerators
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateOneDerivative

/-!
# 元の標準 HT 写像の座標外積上の自然性

## 概要
元の標準 HT 写像と係数変更の可換式を、座標一次形式の外積へ延ばす。

## 方針
元の座標 Bockstein の式と、元の cup 積の自然性を使う。

## 規約
同じ完備化単位を通した標準 HT 写像を使い、同型を選び直さない。

## 使われ方
特定の Zp 係数変更での単項式・外積基底上の照合。
-/

public noncomputable section
universe u
open SerrePositivity.DeRham SerrePositivity.Cosimplicial
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の標準 HT 写像を、元の通常形式の完備化単位の後で読む。 -/
def affineHTRawMap (i : ℕ) :
    forms (A ⧸ P.ideal) (formVars.{u} r) i →+ hodgeTateCohomology' P hP r i :=
  ((hodgeTateMap P hP r).app i).toAddMonoidHom.comp
    (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} r) p i)

private theorem affineHTRawMap_cast {i j : ℕ} (h : i = j)
    (w : forms (A ⧸ P.ideal) (formVars.{u} r) i) :
    affineHTRawMap P hP r j (cast (congrArg (forms (A ⧸ P.ideal) (formVars.{u} r)) h) w) =
      cast (congrArg (hodgeTateCohomology' P hP r) h) (affineHTRawMap P hP r i w) := by
  subst j
  rfl

/-- 同じ通常形式の HT 写像は、元の外積を元の cup 積へ送る。 -/
theorem affineHTRawMap_product {i j : ℕ}
    (x : forms (A ⧸ P.ideal) (formVars.{u} r) i)
    (y : forms (A ⧸ P.ideal) (formVars.{u} r) j) :
    affineHTRawMap P hP r (i + j) (wedge _ _ x y) =
      cohomologyCup (reducedModel P hP r) (affineHTRawMap P hP r i x)
        (affineHTRawMap P hP r j y) := by
  change (hodgeTateMap P hP r).app (i + j) (completedFormsUnit _ _ p _ (wedge _ _ x y)) = _
  rw [← completedWedge_unit]
  exact (hodgeTateMap P hP r).product _ _

/-- 座標一次形式の値は、元の座標零次類の指定された Bockstein。 -/
theorem affineHTRawMap_coordinate (t : formVars.{u} r) :
    affineHTRawMap P hP r 1 (dX (A ⧸ P.ideal) (formVars.{u} r) t) =
      htBocksteinZero P hP r (prismPolynomialUnit P (Fin r) (MvPolynomial.X t.down)) := by
  cases t with
  | up t =>
    change (hodgeTateMap P hP r).app 1 _ = _
    rw [(hodgeTateMap P hP r).on_one]
    change htOneOnGenerators P hP r (affineCoordinateFormOne P r t) = _
    exact htOneOnGenerators_coordinate P hP r t

variable {P} {Q : OrientedPrism p B} (f : OrientedPrism.Hom P Q)
variable (hQ : IsBoundedPrism Q) (hg : f.toRingHom P.generator = Q.generator)

private theorem affineRawCoefficientCohomology_cast {i j : ℕ} (h : i = j)
    (z : hodgeTateCohomology' P hP r i) :
    cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) j
        (cast (congrArg (hodgeTateCohomology' P hP r) h) z) =
      cast (congrArg (hodgeTateCohomology' Q hQ r) h)
        (cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) i z) := by
  subst j
  rfl

/-- 同じ座標一次形式で、元の標準 HT 写像は係数変更と可換。 -/
theorem affineHTRawMap_coordinate_natural (t : formVars.{u} r) :
    cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) 1
      (affineHTRawMap P hP r 1 (dX (A ⧸ P.ideal) (formVars.{u} r) t)) =
      affineHTRawMap Q hQ r 1 (dX (B ⧸ Q.ideal) (formVars.{u} r) t) := by
  rw [affineHTRawMap_coordinate, affineHTRawMap_coordinate,
    affineHTCoefficient_htBocksteinZero, affinePolynomialCoefficientMap_X]

/-- 同じ順序付き座標外積で、元の標準 HT 写像は係数変更と可換。 -/
theorem affineHTRawMap_word_natural (n : ℕ) (v : Fin n → formVars.{u} r)
    (g : Poly (A ⧸ P.ideal) (formVars.{u} r)) :
    cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) n
      (affineHTRawMap P hP r n (coordinateFormWord _ _ n v g)) =
      affineHTRawMap Q hQ r n
        (coordinateFormWord _ _ n v (MvPolynomial.map f.quotientMap g)) := by
  induction n with
  | zero =>
    simpa only [coordinateFormWord_zero, affineHTRawMap, AddMonoidHom.comp_apply,
      LinearMap.toAddMonoidHom_coe] using affineHTRaw_zero_natural hP r f hQ hg g
  | succ n ih =>
    rw [coordinateFormWord_succ, coordinateFormWord_succ,
      affineHTRawMap_cast, affineHTRawMap_cast, affineRawCoefficientCohomology_cast,
      affineHTRawMap_product, affineHTRawMap_product, cohomologyMap_cup,
      affineHTRawMap_coordinate_natural, ih]
    all_goals omega

/-- 元の単項式・外積基底全体で、同じ標準 HT 写像は係数変更と可換。 -/
theorem affineHTRawMap_basis_natural (i : ℕ)
    (v : (formVars.{u} r →₀ ℕ) × Set.powersetCard (formVars.{u} r) i) :
    cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) i
      (affineHTRawMap P hP r i (polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} r) i v)) =
      affineHTRawMap Q hQ r i (polynomialFormsBasis (B ⧸ Q.ideal) (formVars.{u} r) i v) := by
  rw [polynomialFormsBasis_coordinateFormWord, polynomialFormsBasis_coordinateFormWord]
  simpa only [MvPolynomial.map_monomial, map_one] using
    affineHTRawMap_word_natural hP r f hQ hg i
      (Set.powersetCard.ofFinEmbEquiv.symm v.2) (MvPolynomial.monomial v.1 1)

end SerrePositivity.BhattScholze.Prismatic
