module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedCoefficientDiagram
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCohomologyScalarClasses
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBasePolynomialAction
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientDiagram
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZero
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels

/-!
# 元の向きの単位を追った Bockstein の係数自然性

## 概要
生成元を d↦d' u と移す元の prism 射について、Bockstein の比較に単位 u を残す。

## 方針
同じ余鎖を持ち上げ、微分を d' で割る際に現れる u の類を元の係数作用で読む。

## 規約
target の Bockstein は、source の Bockstein の係数像の u 倍である。
単位係数を 1 と仮定しない。

## 使われ方
Construction 6.1 の α による標準 η の比較。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic
open SerrePositivity.Cosimplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)

/-- 元の生成元を単位 u 倍で移すとき、Bockstein の自然性の係数は u である。 -/
theorem affineHTCoefficientReducedAny_bockstein_unit (u : Bˣ)
    (hu : f.toRingHom P.generator = Q.generator * (u : B)) (i : ℕ)
    (a : hodgeTateCohomology' P hP r i) :
    letI := htModule Q hQ r (i + 1)
    bockstein Q hQ r i (cohomologyMap _ _ (affineHTCoefficientReducedAny f hP hQ r) i a) =
      affineBaseToPolynomialMap Q r (u : B) •
        cohomologyMap _ _ (affineHTCoefficientReducedAny f hP hQ r) (i + 1)
          (bockstein P hP r i a) := by
  letI := htModule Q hQ r (i + 1)
  let C := htRings P hP r
  let D := htRings Q hQ r
  let d := htGenerator P hP r
  let e := htGenerator Q hQ r
  let g := affineHTCoefficientRings f hP hQ r
  let q := affineHTCoefficientReducedAny f hP hQ r
  let πC := quotProjection C d (htGenerator_nat P hP r) 1
  let πD := quotProjection D e (htGenerator_nat Q hQ r) 1
  have hq (n : SimplexCategory) (z : C.obj n) : πD.app n (g.app n z) = q.app n (πC.app n z) := rfl
  have hgen (n : SimplexCategory) :
      g.app n (d n) = e n * (htBase Q hQ r).app n (u : B) := by
    change (affineHTCoefficientRings f hP hQ r).app n
      ((htBase P hP r).app n P.generator) = _
    rw [affineHTCoefficientRings_base, hu, map_mul]
  obtain ⟨a, rfl⟩ := cohomologyClass_surjective (reducedModel P hP r) i a
  obtain ⟨x, y, hx, hxy⟩ := exists_regularCocycleLift C d (htGenerator_nat P hP r) i a
  let b := projectCycle C d (htGenerator_nat P hP r) (i + 1) y
    (cochainDifferential_eq_zero_of_eq_mul C d (htGenerator_nat P hP r)
      (htGenerator_regular P hP r) i x y hxy)
  let y' : D.obj ⦋i + 1⦌ := (htBase Q hQ r).app ⦋i + 1⦌ (u : B) * g.app ⦋i + 1⦌ y
  have hdx : cochainDifferential D i (g.app ⦋i⦌ x) = e ⦋i + 1⦌ * y' := by
    rw [← cochainDifferential_natural C D g i, hxy, map_mul, hgen, mul_assoc]
  let b' := projectCycle D e (htGenerator_nat Q hQ r) (i + 1) y'
    (cochainDifferential_eq_zero_of_eq_mul D e (htGenerator_nat Q hQ r)
      (htGenerator_regular Q hQ r) i (g.app ⦋i⦌ x) y' hdx)
  have hx' : πD.app ⦋i⦌ (g.app ⦋i⦌ x) = (cocycleMap _ _ q i a).1 := by
    rw [hq, hx]
    rfl
  have hs := cupBockstein_class C d (htGenerator_nat P hP r) (htGenerator_regular P hP r)
    A (htBase P hP r) i a b x y hx rfl hxy
  have ht := cupBockstein_class D e (htGenerator_nat Q hQ r) (htGenerator_regular Q hQ r)
    B (htBase Q hQ r) i (cocycleMap _ _ q i a) b' (g.app ⦋i⦌ x) y' hx' rfl hdx
  change cupBockstein D e (htGenerator_nat Q hQ r) (htGenerator_regular Q hQ r) B
      (htBase Q hQ r) i (cohomologyMap _ _ q i (cohomologyClass _ i a)) =
    affineBaseToPolynomialMap Q r (u : B) • cohomologyMap _ _ q (i + 1)
      (cupBockstein C d (htGenerator_nat P hP r) (htGenerator_regular P hP r) A
        (htBase P hP r) i (cohomologyClass _ i a))
  rw [hs, cohomologyMap_class, cohomologyMap_class, ht]
  symm
  apply affineHTCohomology_smul_class Q hQ r (i + 1)
  change πD.app ⦋i + 1⦌ y' =
    (affineHTCoefficients Q hQ r).app ⦋i + 1⦌ (affineBaseToPolynomialMap Q r (u : B)) *
      q.app ⦋i + 1⦌ (πC.app ⦋i + 1⦌ y)
  rw [affineHTCoefficients_base]
  change πD.app ⦋i + 1⦌ ((htBase Q hQ r).app ⦋i + 1⦌ (u : B) * g.app ⦋i + 1⦌ y) =
    πD.app ⦋i + 1⦌ ((htBase Q hQ r).app ⦋i + 1⦌ (u : B)) * q.app ⦋i + 1⦌ (πC.app ⦋i + 1⦌ y)
  rw [map_mul, hq]

end SerrePositivity.BhattScholze.Prismatic
