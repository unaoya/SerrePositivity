module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineBaseRealization
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineAnyExtendedHomology
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.HomologyUnitNaturalityValue
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryHomology

/-!
# 元のηの通常被覆像の零次・一次の類

## 概要
元のηの通常係数拡大を指定基底座標で読み、元のHT類の係数変更と照合する。

## 方針
同じηの実現の式を随伴単位の自然性で移し、元の余輪体の類の比較を使う。

## 規約
ηの係数変更に関する自然性も、係数拡大一般の完全性も仮定しない。

## 使われ方
元の単項式・外積基底で、被覆像のηの擬同型性を検査する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory HomologicalComplex
open scoped TensorProduct ChangeOfRings
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded SerrePositivity.DeRham HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hg : Q.generator = (p : B))
variable (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1)

/-- 元のηの通常係数拡大を、同じ元の被覆上の基底係数複体へ移した射。 -/
def affineLineOrdinaryBaseRealization :
    baseChange f.toRingHom (affineComplexOnBase P 1 (affineLineFormalModel P)) ⟶
      (affineBaseComplex Q hQ 1).extend ComplexShape.embeddingUpNat :=
  ((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).map
      ((affineRestrictedComplexFunctor P 1).map η ≫ (affineOriginalBaseComplexIso P hP 1).hom) ≫
    (SerrePositivity.mapExtendIso (ModuleCat.extendScalars f.toRingHom)
      (affineBaseComplex P hP 1) ComplexShape.embeddingUpNat).hom ≫
    extendMap (affineAnyOrdinaryComplexIso f hP hQ hg 1).hom ComplexShape.embeddingUpNat

/-- 元の零次実現の通常被覆像は、同じ元のHT類の係数変更である。 -/
theorem affineLineOrdinaryBaseRealization_zero
    (hη : (affineLineFormalZeroIso P).hom ≫ homologyMap η 0 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 0))
    (w : forms (A ⧸ P.ideal) (formVars.{u} 1) 0) :
    ((affineBaseComplex Q hQ 1).extendHomologyIso ComplexShape.embeddingUpNat (j := 0) (j' := (0 : ℤ)) rfl).hom
      (homologyMap (affineLineOrdinaryBaseRealization f hP hQ hg η) 0
        ((affineLineFormalOrdinaryZeroIso P f.toRingHom).hom
          ((1 : B) ⊗ₜ[A,f.toRingHom] completedFormsUnit (A ⧸ P.ideal) (formVars.{u} 1) p 0 w))) =
      affineNativeBaseCohomologyEquiv Q hQ 1 0
        (SerrePositivity.Cosimplicial.cohomologyMap _ _
          (affineHTCoefficientReducedAny f hP hQ 1) 0 (affineHTRawMap P hP 1 0 w)) := by
  let e := (affineBaseComplex Q hQ 1).extendHomologyIso
    ComplexShape.embeddingUpNat (j := 0) (j' := (0 : ℤ)) rfl
  let η' := (affineRestrictedComplexFunctor P 1).map η ≫ (affineOriginalBaseComplexIso P hP 1).hom
  let g := (SerrePositivity.mapExtendIso (ModuleCat.extendScalars f.toRingHom)
    (affineBaseComplex P hP 1) ComplexShape.embeddingUpNat).hom ≫
    extendMap (affineAnyOrdinaryComplexIso f hP hQ hg 1).hom ComplexShape.embeddingUpNat
  change e.hom (homologyMap
    (((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).map η' ≫ g) 0 _) = _
  rw [homologyMap_comp]
  change e.hom (homologyMap g 0
    (homologyMap (((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).map η') 0
      (complexBaseChangeHomologyComparison f.toRingHom
        (affineComplexOnBase P 1 (affineLineFormalModel P)) 0
        ((1 : B) ⊗ₜ[A,f.toRingHom] (affineLineFormalRestrictedZeroIso P).hom
          (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} 1) p 0 w))))) = _
  rw [complexBaseChangeHomologyComparison_naturality_one_tmul,
    affineLineBaseRealization_zero P hP η hη w]
  exact affineAnyExtendedHomology_one_tmul f hP hQ hg 1 0 _

/-- 元の一次実現の通常被覆像も、同じ元のHT類の係数変更である。 -/
theorem affineLineOrdinaryBaseRealization_one
    (hη : (affineLineFormalOneIso P).hom ≫ homologyMap η 1 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 1))
    (w : forms (A ⧸ P.ideal) (formVars.{u} 1) 1) :
    ((affineBaseComplex Q hQ 1).extendHomologyIso ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) rfl).hom
      (homologyMap (affineLineOrdinaryBaseRealization f hP hQ hg η) 1
        ((affineLineFormalOrdinaryOneIso P f.toRingHom).hom
          ((1 : B) ⊗ₜ[A,f.toRingHom] completedFormsUnit (A ⧸ P.ideal) (formVars.{u} 1) p 1 w))) =
      affineNativeBaseCohomologyEquiv Q hQ 1 1
        (SerrePositivity.Cosimplicial.cohomologyMap _ _
          (affineHTCoefficientReducedAny f hP hQ 1) 1 (affineHTRawMap P hP 1 1 w)) := by
  let e := (affineBaseComplex Q hQ 1).extendHomologyIso
    ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) rfl
  let η' := (affineRestrictedComplexFunctor P 1).map η ≫ (affineOriginalBaseComplexIso P hP 1).hom
  let g := (SerrePositivity.mapExtendIso (ModuleCat.extendScalars f.toRingHom)
    (affineBaseComplex P hP 1) ComplexShape.embeddingUpNat).hom ≫
    extendMap (affineAnyOrdinaryComplexIso f hP hQ hg 1).hom ComplexShape.embeddingUpNat
  change e.hom (homologyMap
    (((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).map η' ≫ g) 1 _) = _
  rw [homologyMap_comp]
  change e.hom (homologyMap g 1
    (homologyMap (((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).map η') 1
      (complexBaseChangeHomologyComparison f.toRingHom
        (affineComplexOnBase P 1 (affineLineFormalModel P)) 1
        ((1 : B) ⊗ₜ[A,f.toRingHom] (affineLineFormalRestrictedOneIso P).hom
          (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} 1) p 1 w))))) = _
  rw [complexBaseChangeHomologyComparison_naturality_one_tmul,
    affineLineBaseRealization_one P hP η hη w]
  exact affineAnyExtendedHomology_one_tmul f hP hQ hg 1 1 _

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
