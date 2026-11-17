module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineAnyOrdinaryTargetUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.OrdinaryExtendedHomology

/-!
# 元の通常被覆ホモロジーの純テンソル上のHT係数類

## 概要
元の零延長の通常比較は、同じ元の剰余係数射の類を一との純テンソルから運ぶ。

## 方針
元の各行の単位と、元の基底係数のコホモロジー類の照合を合成する。

## 規約
始域の生成元をpに制限せず、平坦性も仮定しない。

## 使われ方
元のηの零次・一次の被覆像を、同じ向きの単位を保つHT写像へ比較する。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
open scoped TensorProduct ChangeOfRings
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hg : Q.generator = (p : B)) (r i : ℕ)

/-- 元の零延長の通常比較は、元の同じ係数変更の類を運ぶ。 -/
theorem affineAnyExtendedHomology_one_tmul (z : hodgeTateCohomology' P hP r i) :
    ((affineBaseComplex Q hQ r).extendHomologyIso ComplexShape.embeddingUpNat (j := i) (j' := (i : ℤ)) rfl).hom
      (homologyMap ((SerrePositivity.mapExtendIso (ModuleCat.extendScalars f.toRingHom)
          (affineBaseComplex P hP r) ComplexShape.embeddingUpNat).hom ≫
          extendMap (affineAnyOrdinaryComplexIso f hP hQ hg r).hom
            ComplexShape.embeddingUpNat) (i : ℤ)
        (complexBaseChangeHomologyComparison f.toRingHom
          ((affineBaseComplex P hP r).extend ComplexShape.embeddingUpNat) (i : ℤ)
          ((1 : B) ⊗ₜ[A,f.toRingHom]
            ((affineBaseComplex P hP r).extendHomologyIso
              ComplexShape.embeddingUpNat (j := i) (j' := (i : ℤ)) rfl).inv
              (affineNativeBaseCohomologyEquiv P hP r i z)))) =
      affineNativeBaseCohomologyEquiv Q hQ r i
        (SerrePositivity.Cosimplicial.cohomologyMap _ _
          (affineHTCoefficientReducedAny f hP hQ r) i z) := by
  rw [ordinaryExtendedHomology_one_tmul f.toRingHom (affineBaseComplex P hP r)
    (affineBaseComplex Q hQ r) (affineAnyOrdinaryComplexIso f hP hQ hg r).hom
    (affineAnyBaseRestrictedComplexMap f hP hQ r) (affineAnyOrdinaryComplexIso_unit f hP hQ hg r)]
  rw [affineAnyBaseRestrictedComplexMap_cohomology]
  exact ConcreteCategory.congr_hom
    (((affineBaseComplex Q hQ r).sc i).mapHomologyIso
      (ModuleCat.restrictScalars f.toRingHom)).inv_hom_id _

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
