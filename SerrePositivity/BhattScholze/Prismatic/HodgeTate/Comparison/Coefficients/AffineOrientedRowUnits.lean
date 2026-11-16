module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedBaseRows

/-!
# 元の向き付き行比較の純テンソル上の値

## 概要
随伴で延長した元の行射は、単位純テンソル上で元の剰余係数射そのものとなる。

## 方針
元の係数拡大の純テンソルの式と元の随伴の余単位の値を使う。

## 規約
完備化前の指定射を比較する。同型性や平坦性は仮定しない。

## 使われ方
半自由完備行の標準比較のH⁰を、項ごとの指定同型へ照合する。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)

/-- 元の係数制限への線形行射の台関数は、元の剰余係数射そのもの。 -/
theorem affineBaseAnyRestrictedMap_apply (n : SimplexCategory)
    (x : (affineBaseModules P hP r).obj n) :
    (affineBaseAnyRestrictedMap f hP hQ r).app n x =
      (affineHTCoefficientReducedAny f hP hQ r).app n x := rfl

/-- 元の通常係数行射は、元の単位純テンソル上で元の剰余係数射を与える。 -/
theorem affineBaseAnyOrdinaryCoefficientMap_unit (n : SimplexCategory)
    (x : (affineBaseModules P hP r).obj n) :
    (affineBaseAnyOrdinaryCoefficientMap f hP hQ r).app n ((1 : B) ⊗ₜ[A,f.toRingHom] x) =
      (affineHTCoefficientReducedAny f hP hQ r).app n x := by
  change (ModuleCat.extendRestrictScalarsAdj f.toRingHom).counit.app
      ((affineBaseModules Q hQ r).obj n)
      ((ModuleCat.extendScalars f.toRingHom).map ((affineBaseAnyRestrictedMap f hP hQ r).app n)
        ((1 : B) ⊗ₜ[A,f.toRingHom] x)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  erw [ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul]
  rfl

/-- 任意係数の純テンソルの値も、元の標準線形延長の式である。 -/
theorem affineBaseAnyOrdinaryCoefficientMap_tmul (n : SimplexCategory) (b : B)
    (x : (affineBaseModules P hP r).obj n) :
    (affineBaseAnyOrdinaryCoefficientMap f hP hQ r).app n (b ⊗ₜ[A,f.toRingHom] x) =
      b • (show (affineBaseModules Q hQ r).obj n from
        (affineHTCoefficientReducedAny f hP hQ r).app n x) := by
  have he : (b ⊗ₜ[A,f.toRingHom] x) =
      b • ((1 : B) ⊗ₜ[A,f.toRingHom] x) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  change ((affineBaseAnyOrdinaryCoefficientMap f hP hQ r).app n).hom _ = _
  rw [he, map_smul, affineBaseAnyOrdinaryCoefficientMap_unit]

end SerrePositivity.BhattScholze.Prismatic
