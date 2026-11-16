module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryHomology
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.HomologyRealizationBaseChange
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryHomology

/-!
# 元のHT実現の通常係数拡大の正方形

## 概要
零次・一次の元の標準HT写像を実現するηについて、通常係数拡大後の実際のホモロジー射を固定する。

## 方針
完全な係数制限のホモロジー同型と、同じ通常拡大のホモロジー単位の自然性を順に使う。

## 規約
ηの係数変更に関する自然性や、係数拡大一般の完全性は入力にしない。

## 使われ方
同じηを指定被覆で検出する際、元の形式から元のHTホモロジーへの写像を比較する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P)

/-- 元の標準HT写像を元の基底作用に制限した、整数次数のホモロジーへの射。 -/
def affineRestrictedHTTotalMap (r i : ℕ) :
    (ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).obj
      (ModuleCat.of (affineAlgebra P r) (affineForms P r i)) ⟶
        (affineComplexOnBase P r (affineHTTotalComplex P hP r)).homology (i : ℤ) :=
  (ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).map
      (ModuleCat.ofHom (affineHTTotalMap P hP r i)) ≫
    ((restrictCochainHomologyIso (affineBaseToPolynomialMap P r) (i : ℤ)).app
      (affineHTTotalComplex P hP r)).inv

variable (f : A →+* B) (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1)

/-- 元のH₀の実現は、元の通常係数拡大後の実現の同じ正方形を与える。 -/
theorem affineLineOrdinaryRealization_zero
    (hη : (affineLineFormalZeroIso P).hom ≫ homologyMap η 0 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 0)) :
    (affineLineFormalOrdinaryZeroIso P f).hom ≫
        homologyMap (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
          (((ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).mapHomologicalComplex (.up ℤ)).map η)) 0 =
      (ModuleCat.extendScalars f).map (affineRestrictedHTTotalMap P hP 1 0) ≫
        complexBaseChangeHomologyComparison f
          (affineComplexOnBase P 1 (affineHTTotalComplex P hP 1)) 0 := by
  have h := restrictedHomology_realization (affineBaseToPolynomialMap P 1) η 0
    (affineLineFormalZeroIso P).hom (ModuleCat.ofHom (affineHTTotalMap P hP 1 0)) hη
  exact ordinaryHomology_realization f
    (((ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).mapHomologicalComplex (.up ℤ)).map η) 0 (affineLineFormalRestrictedZeroIso P).hom
    (affineRestrictedHTTotalMap P hP 1 0) h

/-- 元のH₁の実現も、同じ通常係数拡大後の実現の正方形を与える。 -/
theorem affineLineOrdinaryRealization_one
    (hη : (affineLineFormalOneIso P).hom ≫ homologyMap η 1 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 1)) :
    (affineLineFormalOrdinaryOneIso P f).hom ≫
        homologyMap (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
          (((ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).mapHomologicalComplex (.up ℤ)).map η)) 1 =
      (ModuleCat.extendScalars f).map (affineRestrictedHTTotalMap P hP 1 1) ≫
        complexBaseChangeHomologyComparison f
          (affineComplexOnBase P 1 (affineHTTotalComplex P hP 1)) 1 := by
  have h := restrictedHomology_realization (affineBaseToPolynomialMap P 1) η 1
    (affineLineFormalOneIso P).hom (ModuleCat.ofHom (affineHTTotalMap P hP 1 1)) hη
  exact ordinaryHomology_realization f
    (((ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).mapHomologicalComplex (.up ℤ)).map η) 1 (affineLineFormalRestrictedOneIso P).hom
    (affineRestrictedHTTotalMap P hP 1 1) h

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
