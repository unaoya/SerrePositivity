module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrientedOrdinaryRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalTotalModel

/-!
# 元の標準通常係数射によるaffine HT複体の同型

## 概要
終域の生成元がpのとき、元の通常係数射は元のaffine HT全複体の通常係数拡大を同型へ移す。

## 方針
同じ各行の通常係数射を自然同型にし、交代余面複体と零延長の指定同型で運ぶ。

## 規約
始域の生成元はpに制限しない。導来係数拡大の標準増大との照合は別に行う。

## 使われ方
元のηの普通の係数拡大の値を、被覆上の元の標準HT写像と比較する。
-/

public noncomputable section
universe u
open CategoryTheory AlgebraicTopology
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HTComparisonTotal HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hg : Q.generator = (p : B)) (r : ℕ)

include hg
/-- 元の標準通常係数射を、同じ余単体的加群の自然同型として読む。 -/
def affineAnyOrdinaryRowsIso :
    affineBaseModules P hP r ⋙ ModuleCat.extendScalars f.toRingHom ≅ affineBaseModules Q hQ r :=
  NatIso.ofComponents (fun n => by
    haveI := affineBaseAnyOrdinaryCoefficientMap_app_isIso f hP hQ hg r n
    exact asIso ((affineBaseAnyOrdinaryCoefficientMap f hP hQ r).app n))
    (by
      intro m n θ
      exact (affineBaseAnyOrdinaryCoefficientMap f hP hQ r).naturality θ)

/-- 元の標準通常係数射は、同じ交代余面複体の係数拡大にも同型を与える。 -/
def affineAnyOrdinaryComplexIso :
    ((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℕ)).obj
      (affineBaseComplex P hP r) ≅ affineBaseComplex Q hQ r :=
  (alternatingCofaceFunctorIso (ModuleCat.extendScalars f.toRingHom)).app (affineBaseModules P hP r) ≪≫
    (alternatingCofaceMapComplex (ModuleCat.{u} B)).mapIso (affineAnyOrdinaryRowsIso f hP hQ hg r)

/-- 元の全複体の基底作用への制限と、同じ交代余面複体の零延長との指定同型。 -/
def affineOriginalBaseComplexIso (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) :
    affineComplexOnBase P r (affineHTTotalComplex P hP r) ≅
      (affineBaseComplex P hP r).extend ComplexShape.embeddingUpNat :=
  (affineBaseSingleTotalPolynomialIso P hP r).symm ≪≫
    coefficientSingleTotalIso (affineBaseModules P hP r)

/-- 元の標準係数射は、元のHT全複体の通常係数拡大の指定された同型を与える。 -/
def affineAnyOrdinaryTotalIso :
    ((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).obj
        (affineComplexOnBase P r (affineHTTotalComplex P hP r)) ≅
      affineComplexOnBase Q r (affineHTTotalComplex Q hQ r) :=
  ((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).mapIso
      (affineOriginalBaseComplexIso P hP r) ≪≫
    SerrePositivity.mapExtendIso (ModuleCat.extendScalars f.toRingHom) (affineBaseComplex P hP r)
      ComplexShape.embeddingUpNat ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} B)).mapIso
      (affineAnyOrdinaryComplexIso f hP hQ hg r) ≪≫
    (affineOriginalBaseComplexIso Q hQ r).symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
