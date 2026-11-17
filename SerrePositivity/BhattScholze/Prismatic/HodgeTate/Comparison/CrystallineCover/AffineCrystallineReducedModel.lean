module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 結晶的な affine 剰余模型の元の mod p 表示

## 概要
選択生成元が p の場合に、元の Hodge–Tate 剰余模型を同じ affine 項の mod p と同定する。

## 方針
元の基底脚が自然数 p を保つことを使って、商のイデアルの等式を明示する。

## 規約
包や係数射を選び直さない。各次数で元の商射を保つ。

## 使われ方
特定の Zp 係数射による通常の係数拡大を、元の affine 剰余模型に戻す。
-/

public noncomputable section
universe u
open CategoryTheory
open SerrePositivity.Cosimplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)
variable (hg : P.generator = (p : A))
include hg

/-- 結晶的な場合、元の各項の指定生成元は自然数 p の像である。 -/
theorem affineCrystallineGenerator (n : SimplexCategory) : htGenerator P hP r n = (p : _) := by
  change (htBase P hP r).app n P.generator = _
  rw [hg]
  exact map_natCast ((htBase P hP r).app n).hom p

/-- 元の affine 剰余項と、同じ項の通常の mod p の指定された同型。 -/
def affineCrystallineReducedTermEquiv (n : SimplexCategory) :
    (reducedModel P hP r).obj n ≃+*
      ((htRings P hP r).obj n ⧸ Ideal.span {(p : (htRings P hP r).obj n)}) := by
  apply Ideal.quotEquivOfEq
  rw [pow_one, affineCrystallineGenerator P hP r hg n]

/-- この同型は、元の項の商射上で恒等的な代表元を保つ。 -/
theorem affineCrystallineReducedTermEquiv_projection (n : SimplexCategory)
    (x : (htRings P hP r).obj n) :
    affineCrystallineReducedTermEquiv P hP r hg n
        ((quotProjection (htRings P hP r) (htGenerator P hP r)
          (htGenerator_nat P hP r) 1).app n x) =
      Ideal.Quotient.mk _ x := by
  rfl

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
