module

public import SerrePositivity.HomologicalAlgebra.MapExtend
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoefficientSingleRows
public import SerrePositivity.HomologicalAlgebra.ProductTotalSingleRow

/-!
# 元の離散行の積 Tot と交代余面複体

## 概要
元の余単体的加群を零次の single 行へ置いた積 Tot を、元の交代余面複体の零延長へ戻す。

## 方針
交代和と single、零延長と single の元の同型を合成し、縦次数零の指定射影を使う。

## 規約
任意のホモロジー同型を選ばず、元の各次数の射影による複体の同型を使う。

## 使われ方
元の affine の Tot 比較と、標準 HT 写像を持つ元の複体との接続。
-/

public noncomputable section
universe u
open CategoryTheory AlgebraicTopology
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HomologicalAlgebra DifferentialGraded HTComparisonTotal HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

/-- 元の離散行の指定積 Tot は、元の交代余面複体の零延長そのもので計算できる。 -/
def coefficientSingleTotalIso (M : CosimplicialObject (ModuleCat.{u} R)) :
    cosimplicialTotal (coefficientSingleRows M) ≅
      ((alternatingCofaceMapComplex (ModuleCat.{u} R)).obj M).extend ComplexShape.embeddingUpNat :=
  (cochainProductTotalizationFunctor (ModuleCat.{u} R)).mapIso
      ((alternatingCofaceFunctorIso (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0)).app M).symm ≪≫
    (ProductTotal.functor (ModuleCat.{u} R)).mapIso
      (SerrePositivity.mapExtendIso (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0)
        ((alternatingCofaceMapComplex (ModuleCat.{u} R)).obj M) ComplexShape.embeddingUpNat).symm ≪≫
    ProductTotal.singleRowIso
      (((alternatingCofaceMapComplex (ModuleCat.{u} R)).obj M).extend ComplexShape.embeddingUpNat)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
