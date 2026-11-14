module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBigradedLeibniz
public import SerrePositivity.HomologicalAlgebra.BicomplexProductLeibniz
import all SerrePositivity.HomologicalAlgebra.BicomplexProductLeibniz
public import SerrePositivity.HomologicalAlgebra.CochainProduct

/-!
# pd de Rham 総複体の余鎖積

## 概要
総複体の Alexander–Whitney 外積を Leibniz 則を持つ余鎖積としてまとめる。

## 方針
二つの双次数の Leibniz 則と成分を挿入した積の式を使う。

## 規約
総微分は横微分と横次数で符号付けした縦微分。

## 使われ方
pd de Rham 比較の乗法性。
-/

public noncomputable section

open SerrePositivity.HomologicalAlgebra

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

/-- Leibniz 則を持つ pd de Rham 総複体の積。 -/
def pdTotalCochainProduct : CochainProduct (pdDeRhamTotal p k r) where
  mul := pdTotalProduct p k r
  leibniz := totalProduct_leibniz (pdDeRhamDoubleComplex p k r)
    (pdBigradedProduct p k r) (pdTotalProduct p k r)
    (pdTotalProduct_insert p k r) (pdBigradedProduct_horizontal p k r)
    (pdBigradedProduct_vertical p k r)

end SerrePositivity.BhattScholze.Prismatic
