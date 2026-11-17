module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineNativeOrdinaryCoefficientUnit
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineNativeOrdinaryCoefficientUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CompletedCofaceCoefficientFactor
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverResolvedTotal
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverResolvedTotal
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedRowQuasiIso
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CompletedCofaceCoefficientFactor
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.FiniteCompleteSingleRows

/-!
# 元の指定被覆Tot同型の単位上の値

## 概要
元の指定被覆Tot同型を、元の導来単位上で通常の係数射へ戻す。

## 方針
元のκの分解と完備化単位の自然性を使い、終域の同じ単位を消去する。

## 規約
元の指定同型を別の通常係数表示で定義し直さない。

## 使われ方
HT04.R2の元のe_targetの照合。
-/

public noncomputable section
universe u
open CategoryTheory AlgebraicTopology
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HomologicalAlgebra DifferentialGraded DifferentialGraded.ScalarExtension DerivedCompletion
open HTComparisonTotal HTComparisonResolution HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元の通常係数拡大したsingle行の指定Tot係数射。 -/
def affineOrdinaryTotalCoefficient (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) :
    baseChange (Construction61.crystallineCoverMap P).toRingHom
        (cosimplicialTotal (affineBaseSingleRows P hP r)) ⟶
      cosimplicialTotal (affineBaseSingleRows (Construction61.crystallineCover P)
        (Construction61.crystallineCover_bounded P) r) :=
  baseChangeTotalComparison (Construction61.crystallineCoverMap P).toRingHom
      ((alternatingCofaceMapComplex (Complex A)).obj (affineBaseSingleRows P hP r)) ≫
    (cochainProductTotalizationFunctor (ModuleCat.{u} (Construction61.crystallineCoverRing P))).map
      ((alternatingCofaceFunctorIso
        ((ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex
          (.up ℤ))).app (affineBaseSingleRows P hP r)).hom ≫
    (alternatingCofaceMapComplex (Complex (Construction61.crystallineCoverRing P)) ⋙
      cochainProductTotalizationFunctor (ModuleCat.{u} (Construction61.crystallineCoverRing P))).map
      (affineAnyExtendedSingleRowsMap (Construction61.crystallineCoverMap P) hP
        (Construction61.crystallineCover_bounded P) r)

/-- 元の指定被覆Tot同型は、元の単位上で同じ通常Tot係数射になる。 -/
theorem affineNativeCoverTarget_unit (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) :
    let f := Construction61.crystallineCoverMap P
    let X := affineBaseSingleRows P hP r
    (finiteDerivedCompletionUnit (coverImageCoordinates P)).app
      ((complexDerivedExtension f.toRingHom).obj (DerivedCategory.Q.obj (cosimplicialTotal X))) ≫
      cosimplicialNativeCompletedBaseChangeComparison f.toRingHom ![(p : A), P.generator] X 0
        (affineBaseSingleRows_lowerBound P hP r) ≫
      (affineCoverResolvedTotalIso P hP r).hom =
    (complexDerivedExtensionAugmentation f.toRingHom).app (cosimplicialTotal X) ≫
      DerivedCategory.Q.map (affineOrdinaryTotalCoefficient P hP r) := by
  have h := affineNativeTotalIso_unit (Construction61.crystallineCoverMap P) hP
    (Construction61.crystallineCover_bounded P) (Construction61.crystallineCover_generator P) r
    ![(p : A), P.generator] (affineReducedCover_scalarExtensionTorVanishing P hP r)
    (affineCoverRows_complete P r)
  simpa only [affineCoverResolvedTotalIso, affineOrdinaryTotalCoefficient,
    affineOrdinaryCofaceCoefficient, affineBaseSingleRows, coverImageCoordinates] using h

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
