module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedCoefficientDiagram
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedCoefficientDiagram
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientDiagram
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra

/-!
# 元の向き付き係数射の基底線形な行比較

## 概要
生成元を単位倍で移す元のprism射を、元の剰余行の係数制限・係数拡大の標準射として読む。

## 方針
元の基底脚の可換式で線形性を示し、元の係数拡大と制限の随伴の余単位を使う。

## 規約
射の同型性や係数環の平坦性は主張しない。元の剰余係数射を変えない。

## 使われ方
HT04の半自由行の指定された完備底変換の比較射。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)

/-- 元の基底脚は、向きの単位を許す元の剰余係数射とも可換。 -/
theorem affineBaseCoefficientAny_square (n : SimplexCategory) :
    ((affineHTCoefficientReducedAny f hP hQ r).app n).hom.comp
        ((affineBaseCoefficients P hP r).app n).hom =
      ((affineBaseCoefficients Q hQ r).app n).hom.comp f.toRingHom := by
  apply RingHom.ext
  intro a
  exact congrArg ((Cosimplicial.quotProjection (htRings Q hQ r) (htGenerator Q hQ r)
    (htGenerator_nat Q hQ r) 1).app n)
      (affineHTCoefficientRings_base f hP hQ r n a)

/-- 元の剰余係数射を、同じ基底環上での係数制限への線形な行射として読む。 -/
def affineBaseAnyRestrictedMap :
    affineBaseModules P hP r ⟶ affineBaseModules Q hQ r ⋙ ModuleCat.restrictScalars f.toRingHom where
  app n := by
    letI : Module A ((reducedModel P hP r).obj n) :=
      ((affineBaseCoefficients P hP r).app n).hom.toAlgebra.toModule
    letI : Module B ((reducedModel Q hQ r).obj n) :=
      ((affineBaseCoefficients Q hQ r).app n).hom.toAlgebra.toModule
    letI : Module A ((affineBaseModules Q hQ r).obj n) :=
      Module.compHom ((affineBaseModules Q hQ r).obj n) f.toRingHom
    exact ModuleCat.ofHom (show
      ((affineBaseModules P hP r).obj n) →ₗ[A]
        (ModuleCat.restrictScalars f.toRingHom).obj ((affineBaseModules Q hQ r).obj n) from {
      toFun := (affineHTCoefficientReducedAny f hP hQ r).app n
      map_add' := ((affineHTCoefficientReducedAny f hP hQ r).app n).hom.map_add
      map_smul' := fun a x => by
        change (reducedModel P hP r).obj n at x
        change (affineHTCoefficientReducedAny f hP hQ r).app n
            ((affineBaseCoefficients P hP r).app n a * x) =
          (affineBaseCoefficients Q hQ r).app n (f.toRingHom a) *
            (affineHTCoefficientReducedAny f hP hQ r).app n x
        rw [map_mul]
        exact congrArg (fun y => y * (affineHTCoefficientReducedAny f hP hQ r).app n x)
          (RingHom.congr_fun (affineBaseCoefficientAny_square f hP hQ r n) a) })
  naturality m n θ := by
    ext x
    exact ConcreteCategory.congr_hom ((affineHTCoefficientReducedAny f hP hQ r).naturality θ) x

/-- 同じ元の射を、随伴の元の余単位で通常の係数拡大後の線形射へ延長する。 -/
def affineBaseAnyOrdinaryCoefficientMap :
    affineBaseModules P hP r ⋙ ModuleCat.extendScalars f.toRingHom ⟶ affineBaseModules Q hQ r :=
  Functor.whiskerRight (affineBaseAnyRestrictedMap f hP hQ r) (ModuleCat.extendScalars f.toRingHom) ≫
    Functor.whiskerLeft (affineBaseModules Q hQ r) (ModuleCat.extendRestrictScalarsAdj f.toRingHom).counit

end SerrePositivity.BhattScholze.Prismatic
