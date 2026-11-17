module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryTarget
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryTarget
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalTotalModel

/-!
# 元のHT全複体の基底係数への指定座標

## 概要
元のsingle行のTotを介して指定した基底座標を、元の多項式係数複体への射影で表す。

## 方針
同じsingle行のTot同型の往復を消し、元の三つの指定同型を残す。

## 規約
新たな同型を選ばず、元の指定座標の等式を示す。

## 使われ方
元のHT写像の実現を、同じ基底係数のコホモロジー類で計算する。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元の全複体の基底座標は、元の多項式係数複体への指定射影から得る。 -/
theorem affineOriginalBaseComplexIso_eq (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) :
    affineOriginalBaseComplexIso P hP r =
      ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).mapHomologicalComplex (.up ℤ)).mapIso
          (affineHTTotalIso P hP r) ≪≫
        SerrePositivity.mapExtendIso (ModuleCat.restrictScalars (affineBaseToPolynomialMap P r))
          (affineHTComplex P hP r) ComplexShape.embeddingUpNat ≪≫
        (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} A)).mapIso
          (affineBasePolynomialComplexIso P hP r) := by
  apply Iso.ext
  simp [affineOriginalBaseComplexIso, affineBaseSingleTotalPolynomialIso, Category.assoc]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
