module

public import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz
public import SerrePositivity.HomologicalAlgebra.CochainProduct
import all SerrePositivity.CommutativeAlgebra.DeRham.Polynomial

/-!
# 多項式 de Rham コホモロジーの外積

## 概要
微分形式の外積をコホモロジーに降ろす。

## 方針
外積の Leibniz 則を余鎖積の一般の商構成に適用する。

## 規約
外積の因子の順序を保つ。

## 使われ方
Cartier 同型と pd de Rham 比較の乗法性。
-/

public noncomputable section

open CategoryTheory SerrePositivity.HomologicalAlgebra
open scoped TensorProduct

universe u

namespace SerrePositivity.DeRham

variable (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T]

/-- 多項式 de Rham 複体の係数線形な余鎖外積。 -/
def deRhamCochainWedge : CochainProduct (deRhamComplex k T) where
  mul i j := TensorProduct.map₂ (LinearMap.mul k (Poly k T)) (exteriorWedge k (T → k) i j)
  leibniz i j x y := by
    dsimp only [deRhamComplex, CochainComplex.of]
    rw [CochainComplex.of_d, CochainComplex.of_d, CochainComplex.of_d]
    exact deRhamD_wedge k T x y

/-- 多項式 de Rham コホモロジーの積。 -/
def deRhamCohomologyWedge {i j : ℕ} :
    (deRhamComplex k T).homology i → (deRhamComplex k T).homology j →
      (deRhamComplex k T).homology (i + j) :=
  (deRhamCochainWedge k T).onHomology

end SerrePositivity.DeRham
