module

public import SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives
import all SerrePositivity.CommutativeAlgebra.DeRham.Polynomial

/-!
# 座標の冪の整係数 de Rham 微分

## 概要
座標の p 乗の微分を p と Cartier の代表形式の積として書く。

## 方針
多項式偏微分の冪公式で、指定座標以外の項を零にする。

## 規約
次数零の形式への移行は `formsZeroEquiv` を使う。

## 使われ方
結晶基底の Bockstein と一次 Cartier 類の照合。
-/

public noncomputable section

open MvPolynomial
open scoped TensorProduct

universe u

namespace SerrePositivity.DeRham

variable (k T : Type u) [CommRing k] [Fintype T] [DecidableEq T]

/-- 座標の p 乗の微分は p 倍した一次 Cartier 代表形式。 -/
theorem deRhamD_coordinate_pow (p : ℕ) (t : T) :
    deRhamD k T 0 (formsZeroEquiv k T ((X t : Poly k T) ^ p)) =
      p • (((X t : Poly k T) ^ (p-1)) • dX k T t) := by
  rw [formsZeroEquiv_tmul]
  simp only [deRhamD, deRhamDLinear, LinearMap.toAddMonoidHom_coe, LinearMap.sum_apply,
    TensorProduct.map_tmul, Derivation.coeFn_coe]
  rw [Finset.sum_eq_single t]
  · have h : wedgeOne k (T → k) 0 ((exteriorPower.oneEquiv k (T → k)).symm (Pi.single t 1))
        ((exteriorPower.zeroEquiv k (T → k)).symm 1) =
        (exteriorPower.oneEquiv k (T → k)).symm (Pi.single t 1) := by
      apply Subtype.ext
      simp [wedgeOne, exteriorWedge, exteriorPower.zeroEquiv, exteriorPower.oneEquiv_symm_apply,
        ExteriorAlgebra.ιMulti_apply]
    rw [h, pderiv_pow, pderiv_X_self, mul_one]
    change ((p : Poly k T) * X t ^ (p-1)) ⊗ₜ[k] _ = p • ((X t ^ (p-1) * 1) ⊗ₜ[k] _)
    rw [mul_one, ← nsmul_eq_mul]
    let v := (exteriorPower.oneEquiv k (T → k)).symm (Pi.single t 1)
    let L := (TensorProduct.mk k (Poly k T) (⋀[k]^1 (T → k))).flip v
    exact map_nsmul L _ _
  · intro j _ hj
    rw [pderiv_pow, pderiv_X_of_ne hj.symm, mul_zero, TensorProduct.zero_tmul]
  · simp

end SerrePositivity.DeRham
