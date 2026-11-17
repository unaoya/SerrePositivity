module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineCochainModel
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineCochainModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra

/-!
# 元の affine 多項式作用の基底環への制限

## 概要
元の完備多項式作用を基底環へ制限すると、元の基底環上の affine 行模型に一致する。

## 方針
元の包の構造切断の基底脚を使い、同じ台加群の恒等写像を線形同型として束ねる。

## 規約
作用も包も選び直さない。元の構造射の合成として基底環の作用を指定する。

## 使われ方
元の係数線形 HT 写像を、平坦な基底環のコホモロジー比較へ渡す。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の基底環から、元の完備多項式係数環への構造射。 -/
def affineBaseToPolynomialMap : A →+* affineAlgebra P r :=
  (prismPolynomialUnit P (Fin r)).comp (MvPolynomial.C.comp (Ideal.Quotient.mk P.ideal))

/-- 元の多項式係数作用は、基底環に制限すると元の基底脚と一致する。 -/
theorem affineHTCoefficients_base (n : SimplexCategory) (a : A) :
    (affineHTCoefficients P hP r).app n (affineBaseToPolynomialMap P r a) =
      (affineBaseCoefficients P hP r).app n a := by
  apply (htResidueIso P hP r n).injective
  change (htResidueIso P hP r n)
      ((htResidueIso P hP r n).symm
        (((htCech P hP r).obj n).sec (affineBaseToPolynomialMap P r a))) = _
  rw [RingEquiv.apply_symm_apply]
  change ((htCech P hP r).obj n).sec (affineBaseToPolynomialMap P r a) =
    Ideal.Quotient.mk _ (((htCech P hP r).obj n).toHom.toRingHom a)
  exact RingHom.congr_fun ((htCech P hP r).obj n).sec_comp (Ideal.Quotient.mk P.ideal a)

/-- 同じ台の恒等写像は、元の多項式作用の制限と元の基底作用の自然な同型。 -/
def affineBaseModulesPolynomialIso :
    affineBaseModules P hP r ≅
      affineHTModules P hP r ⋙ ModuleCat.restrictScalars (affineBaseToPolynomialMap P r) :=
  NatIso.ofComponents (fun n => by
    let e : (affineBaseModules P hP r).obj n ≃ₗ[A]
        (ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).obj
          ((affineHTModules P hP r).obj n) :=
      { toAddEquiv := AddEquiv.refl ((reducedModel P hP r).obj n)
        map_smul' := fun a x => by
          change (reducedModel P hP r).obj n at x
          change (affineBaseCoefficients P hP r).app n a * x =
            (affineHTCoefficients P hP r).app n (affineBaseToPolynomialMap P r a) * x
          rw [affineHTCoefficients_base] }
    exact e.toModuleIso) (by
      intro m n θ
      ext x
      rfl)

end SerrePositivity.BhattScholze.Prismatic
