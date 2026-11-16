module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedCoefficientRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedRowUnits
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.BaseChangeTotalComparison

import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedCoefficientRows
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoefficientSingleRows
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedBaseRows

/-!
# 元のsingle行の通常係数射と随伴単位

## 概要
元のsingle行の通常係数射を元の随伴単位へ合成すると、同じ元の制限係数射となる。

## 方針
零次成分では元の純テンソルの単位の式、他の成分では元のsingleの零性を使う。

## 規約
生成元を単位倍で移す任意のprism射を扱う。通常係数射の同型性は不要。

## 使われ方
元のHT全複体の通常被覆像の指定同型の単位を、元の係数射へ照合する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory AlgebraicTopology HomologicalComplex
open scoped Simplicial TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HTComparisonTotal HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)

/-- 元の制限係数射を、同じ元のsingle行の射として読む。 -/
def affineAnyRestrictedSingleRowsMap :
    coefficientSingleRows (affineBaseModules P hP r) ⟶
      coefficientSingleRows (affineBaseModules Q hQ r) ⋙
        (ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex (.up ℤ) :=
  Functor.whiskerRight (affineBaseAnyRestrictedMap f hP hQ r)
      (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0) ≫
    Functor.whiskerLeft (affineBaseModules Q hQ r)
      (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars f.toRingHom)
        (.up ℤ) 0).inv

/-- 元のsingle行の通常係数射は、同じ元の随伴単位と元の係数射の正方形を持つ。 -/
theorem affineAnyExtendedSingleRowsMap_unit (n : SimplexCategory) :
    complexBaseChangeUnit f.toRingHom ((coefficientSingleRows (affineBaseModules P hP r)).obj n) ≫
      ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).map
        ((affineAnyExtendedSingleRowsMap f hP hQ r).app n) =
      (affineAnyRestrictedSingleRowsMap f hP hQ r).app n := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = 0
  · subst i
    letI := f.toRingHom.toAlgebra
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((affineBaseAnyOrdinaryCoefficientMap f hP hQ r).app n)
      ((1 : B) ⊗ₜ[A] x) = (affineHTCoefficientReducedAny f hP hQ r).app n x
    exact affineBaseAnyOrdinaryCoefficientMap_unit f hP hQ r n x
  · exact (isZero_single_obj_X (.up ℤ) 0 ((affineBaseModules P hP r).obj n) i hi).eq_of_src _ _

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
