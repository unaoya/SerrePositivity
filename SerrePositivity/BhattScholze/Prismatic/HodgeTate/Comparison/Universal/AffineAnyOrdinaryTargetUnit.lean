module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.OrdinaryExtendedUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineAnyRestrictedCohomologyClasses
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryTarget
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedRowUnits
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryTarget
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineAnyRestrictedCohomologyClasses
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedBaseRows

/-!
# 元の通常HT全複体同型の単位

## 概要
元の剰余係数射から作った通常全複体の同型は、同じ係数制限への射を随伴単位で実現する。

## 方針
元の各行の単位の正方形を零延長へ移し、元の基底座標を前後に合成する。

## 規約
始域の生成元をpに制限せず、元の標準HT写像を変えない。

## 使われ方
元のηの通常被覆像のホモロジー射を、同じ剰余係数射の類と照合する。
-/

public noncomputable section
universe u
open CategoryTheory AlgebraicTopology HomologicalComplex
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HTComparisonTotal HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hg : Q.generator = (p : B)) (r : ℕ)

/-- 元の通常基底複体同型も、元の各項の単位の正方形を持つ。 -/
theorem affineAnyOrdinaryComplexIso_unit (n : ℕ) :
    (ModuleCat.extendRestrictScalarsAdj f.toRingHom).unit.app ((affineBaseComplex P hP r).X n) ≫
        (ModuleCat.restrictScalars f.toRingHom).map
          ((affineAnyOrdinaryComplexIso f hP hQ hg r).hom.f n) =
      (affineAnyBaseRestrictedComplexMap f hP hQ r).f n := by
  letI := f.toRingHom.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (affineBaseAnyOrdinaryCoefficientMap f hP hQ r).app (SimplexCategory.mk n)
    ((1 : B) ⊗ₜ[A] x) = (affineHTCoefficientReducedAny f hP hQ r).app (SimplexCategory.mk n) x
  exact affineBaseAnyOrdinaryCoefficientMap_unit f hP hQ r (SimplexCategory.mk n) x

/-- 元の通常全複体同型の随伴単位は、元の剰余係数射の指定された零延長である。 -/
@[reassoc] theorem affineAnyOrdinaryTotalIso_unit :
    complexBaseChangeUnit f.toRingHom (affineComplexOnBase P r (affineHTTotalComplex P hP r)) ≫
        ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).map
          (affineAnyOrdinaryTotalIso f hP hQ hg r).hom =
      (affineOriginalBaseComplexIso P hP r).hom ≫
        extendMap (affineAnyBaseRestrictedComplexMap f hP hQ r) ComplexShape.embeddingUpNat ≫
        (SerrePositivity.mapExtendIso (ModuleCat.restrictScalars f.toRingHom)
          (affineBaseComplex Q hQ r) ComplexShape.embeddingUpNat).inv ≫
        ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).map
          (affineOriginalBaseComplexIso Q hQ r).inv := by
  have hu := ordinaryExtendedUnit f.toRingHom (affineBaseComplex P hP r) (affineBaseComplex Q hQ r)
    (affineAnyOrdinaryComplexIso f hP hQ hg r).hom
    (affineAnyBaseRestrictedComplexMap f hP hQ r) (affineAnyOrdinaryComplexIso_unit f hP hQ hg r)
  simp only [Functor.map_comp, Category.assoc] at hu
  simp only [affineAnyOrdinaryTotalIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  erw [← Category.assoc, ← complexBaseChangeUnit_naturality, Category.assoc, reassoc_of% hu]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
