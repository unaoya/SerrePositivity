module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoefficientSingleTotalModel
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverTotalization
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineModelsComplete
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseHodgeTateMap

/-!
# 元の affine HT 全複体と基底上の離散行の積 Tot

## 概要
元の完備多項式係数の指定全複体を基底へ制限すると、元の剰余行の指定積 Tot と一致する。

## 方針
元の係数作用の恒等同型、交代余面複体、零延長、縦次数零の指定射影を順に合成する。

## 規約
元の包と係数作用と標準 HT 写像を選び直さない。全て実際の複体の同型である。

## 使われ方
元の affine line の η の終域と HT02 の完備導来底変換–Tot 比較の源を一致させる。
-/

public noncomputable section
universe u
open CategoryTheory AlgebraicTopology
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HTComparisonTotal HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の基底上の離散行の積 Tot は、元の指定 HT 全複体への係数制限と同型。 -/
def affineBaseSingleTotalPolynomialIso :
    cosimplicialTotal (affineBaseSingleRows P hP r) ≅
      affineComplexOnBase P r (affineHTTotalComplex P hP r) :=
  coefficientSingleTotalIso (affineBaseModules P hP r) ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} A)).mapIso
      (affineBasePolynomialComplexIso P hP r).symm ≪≫
    (SerrePositivity.mapExtendIso (ModuleCat.restrictScalars (affineBaseToPolynomialMap P r))
      (affineHTComplex P hP r) ComplexShape.embeddingUpNat).symm ≪≫
    ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).mapHomologicalComplex (.up ℤ)).mapIso
      (affineHTTotalIso P hP r).symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
