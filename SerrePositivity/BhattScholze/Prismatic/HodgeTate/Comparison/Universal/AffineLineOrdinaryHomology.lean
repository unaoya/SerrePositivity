module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineDegrees
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.BaseChangeHomologyZeroDifferential
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineFormalCoverAugmentation

/-!
# 元の二次数形式模型の通常係数拡大のホモロジー

## 概要
元の形式模型での随伴単位によるホモロジー比較は同型で、零次・一次以外の支えを保つ。

## 方針
元の微分の零性により比較を同型にし、完全な係数制限と元の形式模型の指定同型を使う。

## 規約
元の任意のηの自然性や、係数拡大関手一般のホモロジー保存は仮定しない。

## 使われ方
元のηのH₀・H₁の実現を、元の通常被覆係数拡大の同じ正方形へ移す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HTComparisonTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (f : A →+* B)

/-- 元の形式模型では、同じホモロジー単位の転置は全ての整数次数で同型。 -/
theorem affineLineFormalOrdinaryHomologyComparison_isIso (i : ℤ) :
    IsIso (complexBaseChangeHomologyComparison f
      (affineComplexOnBase P 1 (affineLineFormalModel P)) i) := by
  apply complexBaseChangeHomologyComparison_isIso_of_zero_g
  change (ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).map
    ((affineLineFormalModel P).d i ((ComplexShape.up ℤ).next i)) = 0
  rw [affineLineFormal_d_zero, Functor.map_zero]

/-- 同じ元の形式模型の通常係数拡大も、零次・一次以外のホモロジーを持たない。 -/
theorem affineLineFormalOrdinary_homology_isZero (i : ℤ) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    IsZero ((baseChange f (affineComplexOnBase P 1 (affineLineFormalModel P))).homology i) := by
  let U := ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)
  let K := affineLineFormalModel P
  let L := affineComplexOnBase P 1 K
  let e := (K.sc i).mapHomologyIso U
  have hK := affineLineFormal_homology_isZero P i h0 h1
  have hL : IsZero (L.homology i) := (U.map_isZero hK).of_iso e
  have hz := (ModuleCat.extendScalars f).map_isZero hL
  haveI := affineLineFormalOrdinaryHomologyComparison_isIso P f i
  exact hz.of_iso (asIso (complexBaseChangeHomologyComparison f L i)).symm

/-- 元の零次形式から係数制限した元の形式模型のH₀への指定同型。 -/
def affineLineFormalRestrictedZeroIso :
    (ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).obj
      (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 0)) ≅
        (affineComplexOnBase P 1 (affineLineFormalModel P)).homology 0 :=
  (ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).mapIso (affineLineFormalZeroIso P) ≪≫
    (((affineLineFormalModel P).sc 0).mapHomologyIso
      (ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1))).symm

/-- 元の一次形式から係数制限した元の形式模型のH₁への指定同型。 -/
def affineLineFormalRestrictedOneIso :
    (ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).obj
      (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 1)) ≅
        (affineComplexOnBase P 1 (affineLineFormalModel P)).homology 1 :=
  (ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).mapIso (affineLineFormalOneIso P) ≪≫
    (((affineLineFormalModel P).sc 1).mapHomologyIso
      (ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1))).symm

/-- 元の通常係数拡大した零次形式から、元の通常係数拡大した形式模型のH₀への同型。 -/
def affineLineFormalOrdinaryZeroIso :
    (ModuleCat.extendScalars f).obj
      ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).obj
        (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 0))) ≅
      (baseChange f (affineComplexOnBase P 1 (affineLineFormalModel P))).homology 0 := by
  haveI := affineLineFormalOrdinaryHomologyComparison_isIso P f 0
  exact (ModuleCat.extendScalars f).mapIso (affineLineFormalRestrictedZeroIso P) ≪≫
    asIso (complexBaseChangeHomologyComparison f (affineComplexOnBase P 1 (affineLineFormalModel P)) 0)

/-- 元の通常係数拡大した一次形式から、元の通常係数拡大した形式模型のH₁への同型。 -/
def affineLineFormalOrdinaryOneIso :
    (ModuleCat.extendScalars f).obj
      ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).obj
        (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 1))) ≅
      (baseChange f (affineComplexOnBase P 1 (affineLineFormalModel P))).homology 1 := by
  haveI := affineLineFormalOrdinaryHomologyComparison_isIso P f 1
  exact (ModuleCat.extendScalars f).mapIso (affineLineFormalRestrictedOneIso P) ≪≫
    asIso (complexBaseChangeHomologyComparison f (affineComplexOnBase P 1 (affineLineFormalModel P)) 1)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
