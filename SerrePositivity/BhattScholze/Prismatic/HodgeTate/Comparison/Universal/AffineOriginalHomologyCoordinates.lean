module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalBaseCoordinates
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.MapExtendHomologyCompatibility
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryRealization
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineTotalModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseHodgeTateMap

/-!
# 元のHT全複体の基底ホモロジー座標

## 概要
元の全複体の基底座標で、元の指定された多項式係数ホモロジー同型を保持する。

## 方針
完全な係数制限の自然性、零延長比較のホモロジー整合性を順に使う。

## 規約
元のHT写像の定義を変えない。

## 使われ方
ηの元の実現を、同じ剰余余輪体の基底上の類へ戻す。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r n : ℕ)

/-- 元の基底座標は、元の多項式係数の指定ホモロジー同型と可換。 -/
theorem affineOriginalBaseComplexIso_homology :
    homologyMap (affineOriginalBaseComplexIso P hP r).hom (n : ℤ) ≫
        ((affineBaseComplex P hP r).extendHomologyIso
          ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).hom =
      ((restrictCochainHomologyIso (affineBaseToPolynomialMap P r) (n : ℤ)).app
        (affineHTTotalComplex P hP r)).hom ≫
        (ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).map
          (affineHTTotalHomologyIso P hP r n).hom ≫
        (affineBasePolynomialCohomologyIso P hP r n).hom := by
  let U := ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)
  let K := affineHTComplex P hP r
  let KU := (U.mapHomologicalComplex (.up ℕ)).obj K
  let e := ComplexShape.embeddingUpNat
  let t := (affineHTTotalIso P hP r).hom
  let b := (affineBasePolynomialComplexIso P hP r).hom
  let γ := (SerrePositivity.mapExtendIso U K e).hom
  let u := ((K.sc n).mapHomologyIso U)
  have hc : homologyMap γ (n : ℤ) ≫ (KU.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).hom =
      (((K.extend e).sc (n : ℤ)).mapHomologyIso U).hom ≫
        U.map (K.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).hom ≫ u.inv := by
    apply (cancel_mono u.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact mapExtendIso_homology_compatibility U K n
  have hn := (restrictCochainHomologyIso (affineBaseToPolynomialMap P r) (n : ℤ)).hom.naturality t
  change homologyMap ((U.mapHomologicalComplex (.up ℤ)).map t) (n : ℤ) ≫
      (((K.extend e).sc (n : ℤ)).mapHomologyIso U).hom =
    ((restrictCochainHomologyIso (affineBaseToPolynomialMap P r) (n : ℤ)).app
      (affineHTTotalComplex P hP r)).hom ≫ U.map (homologyMap t (n : ℤ)) at hn
  rw [affineOriginalBaseComplexIso_eq]
  simp only [Iso.trans_hom, Functor.mapIso_hom, homologyMap_comp, Category.assoc]
  erw [extendHomologyIso_hom_naturality]
  change homologyMap ((U.mapHomologicalComplex (.up ℤ)).map t) (n : ℤ) ≫
      (homologyMap γ (n : ℤ) ≫ (KU.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).hom) ≫
      homologyMap b n = _
  erw [hc, ← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  change _ = _ ≫ U.map (homologyMap t (n : ℤ) ≫
      (K.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).hom) ≫ (u.inv ≫ homologyMap b n)
  conv_rhs => rw [U.map_comp]
  simp only [Category.assoc]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
