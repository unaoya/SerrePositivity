module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineRestrictedHTCoordinates
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverOrdinaryComparison
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryHomology

/-!
# 元のHT実現を基底係数の余輪体の座標で読む

## 概要
元のηの零次・一次の実現の式を、同じ基底係数複体のホモロジー類へ戻す。

## 方針
元の指定座標と、同じ形式の完備化単位上の標準HT類の照合を使う。

## 規約
ηの自然性を新たに仮定せず、元の実現の等式だけを使う。

## 使われ方
元のηの通常被覆像を、単項式・外積基底上で計算する。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded SerrePositivity.DeRham HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P)

/-- 元の制限実現の式は、元の零延長の指定座標で同じHT類を与える。 -/
theorem affineRestrictedHTRealization_raw {F : Complex A}
    (η : F ⟶ affineComplexOnBase P 1 (affineHTTotalComplex P hP 1)) (i : ℕ)
    (a : (ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).obj
      (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 i)) ⟶ F.homology (i : ℤ))
    (ha : a ≫ homologyMap η (i : ℤ) = affineRestrictedHTTotalMap P hP 1 i)
    (w : forms (A ⧸ P.ideal) (formVars.{u} 1) i) :
    homologyMap (η ≫ (affineOriginalBaseComplexIso P hP 1).hom) (i : ℤ)
        (a (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} 1) p i w)) =
      ((affineBaseComplex P hP 1).extendHomologyIso
        ComplexShape.embeddingUpNat (j := i) (j' := (i : ℤ)) rfl).inv
        (affineNativeBaseCohomologyEquiv P hP 1 i (affineHTRawMap P hP 1 i w)) := by
  have h := ConcreteCategory.congr_hom ha
    (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} 1) p i w)
  change homologyMap η (i : ℤ) (a _) = affineRestrictedHTTotalMap P hP 1 i _ at h
  let e := (affineBaseComplex P hP 1).extendHomologyIso
    ComplexShape.embeddingUpNat (j := i) (j' := (i : ℤ)) rfl
  have hc := ConcreteCategory.congr_hom
    (homologyMap_comp η (affineOriginalBaseComplexIso P hP 1).hom (i : ℤ))
    (a (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} 1) p i w))
  change homologyMap (η ≫ (affineOriginalBaseComplexIso P hP 1).hom) (i : ℤ)
      (a (completedFormsUnit _ _ p i w)) =
    homologyMap (affineOriginalBaseComplexIso P hP 1).hom (i : ℤ)
      (homologyMap η (i : ℤ) (a (completedFormsUnit _ _ p i w))) at hc
  have ht := (congrArg (fun z => e.hom z) hc).trans
    ((congrArg (fun z => e.hom
      (homologyMap (affineOriginalBaseComplexIso P hP 1).hom (i : ℤ) z)) h).trans
      (affineRestrictedHTTotalMap_coordinates_raw P hP 1 i w))
  exact (ModuleCat.inv_hom_apply e _).symm.trans (congrArg (fun z => e.inv z) ht)

variable (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1)

/-- 元の零次実現の式を、元の基底係数の同じHT類へ戻す。 -/
theorem affineLineBaseRealization_zero
    (hη : (affineLineFormalZeroIso P).hom ≫ homologyMap η 0 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 0))
    (w : forms (A ⧸ P.ideal) (formVars.{u} 1) 0) :
    homologyMap (((affineRestrictedComplexFunctor P 1).map η) ≫
        (affineOriginalBaseComplexIso P hP 1).hom) 0
        ((affineLineFormalRestrictedZeroIso P).hom (completedFormsUnit _ _ p 0 w)) =
      ((affineBaseComplex P hP 1).extendHomologyIso ComplexShape.embeddingUpNat (j := 0) (j' := (0 : ℤ)) rfl).inv
        (affineNativeBaseCohomologyEquiv P hP 1 0 (affineHTRawMap P hP 1 0 w)) := by
  exact affineRestrictedHTRealization_raw P hP ((affineRestrictedComplexFunctor P 1).map η) 0
    (affineLineFormalRestrictedZeroIso P).hom
    (restrictedHomology_realization (affineBaseToPolynomialMap P 1) η 0
      (affineLineFormalZeroIso P).hom (ModuleCat.ofHom (affineHTTotalMap P hP 1 0)) hη) w

/-- 元の一次実現の式も、同じ基底係数のHT類へ戻す。 -/
theorem affineLineBaseRealization_one
    (hη : (affineLineFormalOneIso P).hom ≫ homologyMap η 1 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 1))
    (w : forms (A ⧸ P.ideal) (formVars.{u} 1) 1) :
    homologyMap (((affineRestrictedComplexFunctor P 1).map η) ≫
        (affineOriginalBaseComplexIso P hP 1).hom) 1
        ((affineLineFormalRestrictedOneIso P).hom (completedFormsUnit _ _ p 1 w)) =
      ((affineBaseComplex P hP 1).extendHomologyIso ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) rfl).inv
        (affineNativeBaseCohomologyEquiv P hP 1 1 (affineHTRawMap P hP 1 1 w)) := by
  exact affineRestrictedHTRealization_raw P hP ((affineRestrictedComplexFunctor P 1).map η) 1
    (affineLineFormalRestrictedOneIso P).hom
    (restrictedHomology_realization (affineBaseToPolynomialMap P 1) η 1
      (affineLineFormalOneIso P).hom (ModuleCat.ofHom (affineHTTotalMap P hP 1 1)) hη) w

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
