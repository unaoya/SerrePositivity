module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineReducedModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineReducedModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel

/-!
# 元の基底作用を保つ結晶 affine 剰余表示

## 概要
元の affine 剰余模型の mod p 表示を、元の基底環上の代数同型として読む。

## 方針
同じ商射と基底脚で代数構造を指定し、既存の剰余同型が基底脚を保つことを確認する。

## 規約
基底の作用を選び直さず、affineBaseCoefficients が指定した作用を使う。

## 使われ方
項ごとの係数同型を、標準の加群の係数拡大へ渡す。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)
variable (hg : P.generator = (p : A))
include hg

/-- 元の mod p 同型は、元の基底環からの同じ作用を保つ。 -/
def affineCrystallineReducedTermAlgEquiv (n : SimplexCategory) :
    letI : Algebra A ((reducedModel P hP r).obj n) :=
      ((affineBaseCoefficients P hP r).app n).hom.toAlgebra
    letI : Algebra A ((htRings P hP r).obj n ⧸ Ideal.span {(p : (htRings P hP r).obj n)}) :=
      ((Ideal.Quotient.mk (Ideal.span {(p : (htRings P hP r).obj n)})).comp
      ((htBase P hP r).app n).hom).toAlgebra
    (reducedModel P hP r).obj n ≃ₐ[A]
      ((htRings P hP r).obj n ⧸ Ideal.span {(p : (htRings P hP r).obj n)}) := by
  letI : Algebra A ((reducedModel P hP r).obj n) :=
      ((affineBaseCoefficients P hP r).app n).hom.toAlgebra
  letI : Algebra A ((htRings P hP r).obj n ⧸ Ideal.span {(p : (htRings P hP r).obj n)}) :=
      ((Ideal.Quotient.mk (Ideal.span {(p : (htRings P hP r).obj n)})).comp
    ((htBase P hP r).app n).hom).toAlgebra
  exact { __ := affineCrystallineReducedTermEquiv P hP r hg n
          commutes' := fun _ => rfl }

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
