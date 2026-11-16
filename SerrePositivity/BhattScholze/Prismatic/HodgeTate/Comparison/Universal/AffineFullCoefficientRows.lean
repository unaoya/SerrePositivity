module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedCone
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedBaseRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedRowUnits
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedBaseRows
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientDiagram
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleMap
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedCoefficientDiagram

/-!
# 元のfull envelopeの通常係数行射

## 概要
元のfull envelopeの係数射を、係数制限への線形射と通常係数拡大後の射として読む。

## 方針
元の基底脚の等式で線形性を確認し、既存の係数拡大・制限の随伴を使う。

## 規約
元の係数射と商射を変えず、基底の通常の平坦性を仮定しない。

## 使われ方
元のfull envelopeの指定された比較を剰余行へ降ろす。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)

/-- 元のfull envelopeの係数射を係数制限への同じ線形射として読む。 -/
def affineFullAnyRestrictedMap :
    affineFullBaseModules P hP r ⟶
      affineFullBaseModules Q hQ r ⋙ ModuleCat.restrictScalars f.toRingHom where
  app n := by
    letI : Module A ((htRings P hP r).obj n) :=
      ((htBase P hP r).app n).hom.toAlgebra.toModule
    letI : Module B ((htRings Q hQ r).obj n) :=
      ((htBase Q hQ r).app n).hom.toAlgebra.toModule
    letI : Module A ((affineFullBaseModules Q hQ r).obj n) :=
      Module.compHom ((affineFullBaseModules Q hQ r).obj n) f.toRingHom
    exact ModuleCat.ofHom (show
      ((affineFullBaseModules P hP r).obj n) →ₗ[A]
        (ModuleCat.restrictScalars f.toRingHom).obj ((affineFullBaseModules Q hQ r).obj n) from {
      toFun := (affineHTCoefficientRings f hP hQ r).app n
      map_add' := ((affineHTCoefficientRings f hP hQ r).app n).hom.map_add
      map_smul' := fun a x => by
        change (htRings P hP r).obj n at x
        change (affineHTCoefficientRings f hP hQ r).app n ((htBase P hP r).app n a * x) =
          (htBase Q hQ r).app n (f.toRingHom a) * (affineHTCoefficientRings f hP hQ r).app n x
        rw [map_mul, affineHTCoefficientRings_base] })
  naturality m n θ := by
    ext x
    exact ConcreteCategory.congr_hom ((affineHTCoefficientRings f hP hQ r).naturality θ) x

/-- 元のfull envelopeの係数射の同じ標準線形延長。 -/
def affineFullAnyOrdinaryMap :
    affineFullBaseModules P hP r ⋙ ModuleCat.extendScalars f.toRingHom ⟶ affineFullBaseModules Q hQ r :=
  Functor.whiskerRight (affineFullAnyRestrictedMap f hP hQ r) (ModuleCat.extendScalars f.toRingHom) ≫
    Functor.whiskerLeft (affineFullBaseModules Q hQ r) (ModuleCat.extendRestrictScalarsAdj f.toRingHom).counit

/-- 元の商射は係数制限への同じfull envelopeの射と可換。 -/
theorem affineFullBaseProjection_restricted (n : SimplexCategory) :
    (affineFullAnyRestrictedMap f hP hQ r).app n ≫
      (ModuleCat.restrictScalars f.toRingHom).map ((affineFullBaseProjection Q hQ r).app n) =
    (affineFullBaseProjection P hP r).app n ≫ (affineBaseAnyRestrictedMap f hP hQ r).app n := by
  ext x
  rfl

/-- 同じ通常係数拡大後のfull envelopeの射は単位純テンソルを保つ。 -/
theorem affineFullAnyOrdinaryMap_unit (n : SimplexCategory)
    (x : (affineFullBaseModules P hP r).obj n) :
    (affineFullAnyOrdinaryMap f hP hQ r).app n ((1 : B) ⊗ₜ[A,f.toRingHom] x) =
      (affineHTCoefficientRings f hP hQ r).app n x := by
  change (ModuleCat.extendRestrictScalarsAdj f.toRingHom).counit.app _
    ((ModuleCat.extendScalars f.toRingHom).map ((affineFullAnyRestrictedMap f hP hQ r).app n)
      ((1 : B) ⊗ₜ[A,f.toRingHom] x)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  erw [ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul]
  rfl

/-- 純テンソルの元の係数像は、元のB線形延長である。 -/
theorem affineFullAnyOrdinaryMap_tmul (n : SimplexCategory) (b : B)
    (x : (affineFullBaseModules P hP r).obj n) :
    (affineFullAnyOrdinaryMap f hP hQ r).app n (b ⊗ₜ[A,f.toRingHom] x) =
      b • (show (affineFullBaseModules Q hQ r).obj n from
        (affineHTCoefficientRings f hP hQ r).app n x) := by
  have he : b ⊗ₜ[A,f.toRingHom] x = b • ((1 : B) ⊗ₜ[A,f.toRingHom] x) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  change ((affineFullAnyOrdinaryMap f hP hQ r).app n).hom _ = _
  rw [he, map_smul, affineFullAnyOrdinaryMap_unit]

/-- 元の通常係数拡大後にも、同じfull envelopeの係数射は元の商射と可換。 -/
theorem affineFullBaseProjection_ordinary (n : SimplexCategory) :
    (ModuleCat.extendScalars f.toRingHom).map ((affineFullBaseProjection P hP r).app n) ≫
      (affineBaseAnyOrdinaryCoefficientMap f hP hQ r).app n =
    (affineFullAnyOrdinaryMap f hP hQ r).app n ≫ (affineFullBaseProjection Q hQ r).app n := by
  apply ((ModuleCat.extendRestrictScalarsAdj f.toRingHom).homEquiv
    ((affineFullBaseModules P hP r).obj n) ((affineBaseModules Q hQ r).obj n)).injective
  ext x
  change (affineBaseAnyOrdinaryCoefficientMap f hP hQ r).app n
      ((ModuleCat.extendScalars f.toRingHom).map ((affineFullBaseProjection P hP r).app n)
        ((1 : B) ⊗ₜ[A,f.toRingHom] x)) =
    (affineFullBaseProjection Q hQ r).app n
      ((affineFullAnyOrdinaryMap f hP hQ r).app n ((1 : B) ⊗ₜ[A,f.toRingHom] x))
  rw [ModuleCat.ExtendScalars.map_tmul, affineBaseAnyOrdinaryCoefficientMap_unit,
    affineFullAnyOrdinaryMap_unit]
  rfl

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
