module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalHomologyCoordinates
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineBasePolynomialCohomologyClasses
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryRealization
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineCochainMap
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawHodgeTateWords
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawHodgeTateWords
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineTotalModel

/-!
# 元のHT写像の基底座標での値

## 概要
元の全複体に実現したHT写像を、同じ基底係数の指定座標へ移す。

## 方針
元の全複体の指定ホモロジー座標と、元の多項式係数の類の照合を合成する。

## 規約
元の標準HT写像のままで、任意のホモロジー写像へ置き換えない。

## 使われ方
元のηの実現の式を、指定被覆での単項式・外積基底の計算へ接続する。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open SerrePositivity.DeRham HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r n : ℕ)

/-- 元のHT全複体の指定座標で、元の多項式係数HT写像を保つ。 -/
theorem affineRestrictedHTTotalMap_coordinates :
    affineRestrictedHTTotalMap P hP r n ≫
        homologyMap (affineOriginalBaseComplexIso P hP r).hom (n : ℤ) ≫
        ((affineBaseComplex P hP r).extendHomologyIso
          ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).hom =
      (ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).map
        (ModuleCat.ofHom (affineHTMap P hP r n)) ≫
        (affineBasePolynomialCohomologyIso P hP r n).hom := by
  let U := ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)
  have hHT : ModuleCat.ofHom (affineHTTotalMap P hP r n) ≫
      (affineHTTotalHomologyIso P hP r n).hom = ModuleCat.ofHom (affineHTMap P hP r n) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact affineHTTotalMap_projection P hP r n x
  erw [affineOriginalBaseComplexIso_homology]
  simp only [affineRestrictedHTTotalMap, Category.assoc, Iso.inv_hom_id_assoc]
  erw [← Category.assoc, ← U.map_comp, hHT]

/-- 元の通常形式の完備化単位の像では、元の同じHT類の基底係数表示になる。 -/
theorem affineRestrictedHTTotalMap_coordinates_raw
    (w : forms (A ⧸ P.ideal) (formVars.{u} r) n) :
    ((affineBaseComplex P hP r).extendHomologyIso
        ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).hom
      (homologyMap (affineOriginalBaseComplexIso P hP r).hom (n : ℤ)
        (affineRestrictedHTTotalMap P hP r n
          (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} r) p n w))) =
      affineNativeBaseCohomologyEquiv P hP r n (affineHTRawMap P hP r n w) := by
  have h := ConcreteCategory.congr_hom (affineRestrictedHTTotalMap_coordinates P hP r n)
    (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} r) p n w)
  change _ = (affineBasePolynomialCohomologyIso P hP r n).hom
    (affineHTCohomologyEquiv P hP r n (affineHTRawMap P hP r n w)) at h
  exact h.trans (affineBasePolynomialCohomologyIso_cohomology P hP r n _)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
