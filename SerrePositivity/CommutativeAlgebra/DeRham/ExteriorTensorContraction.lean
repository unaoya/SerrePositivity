module

public import SerrePositivity.CommutativeAlgebra.DeRham.ExteriorContraction
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# 係数微分と外冪の収縮

## 概要
一つの座標について、積分作用素と外冪の内部積をテンソルし、微分との反交換子を計算する。

## 方針
外積と内部積の反交換公式を使い、指定座標以外の項を打ち消す。

## 規約
微分は対応する一次形式を左から外積する。

## 使われ方
pd Poincaré 補題と Cartier の指数分解。
-/

public noncomputable section

open scoped TensorProduct

universe u v

namespace SerrePositivity.DeRham

variable {k : Type u} [CommRing k] {M A : Type u} [AddCommGroup M] [Module k M]
  [AddCommGroup A] [Module k A] {S : Type v} [Fintype S]

variable (b : Module.Basis S k M)

/-- 基底の一次形式を左から外積する。 -/
def basisWedgeOne (j : ℕ) (s : S) : (⋀[k]^j M) →ₗ[k] (⋀[k]^(j+1) M) :=
  wedgeOne k M j ((exteriorPower.oneEquiv k M).symm (b s))

/-- 基底に双対な座標汎関数で収縮する。 -/
abbrev basisContract (j : ℕ) (s : S) := exteriorContract k M (b.coord s) j

omit [Fintype S] in
private theorem basisContract_wedgeOne [DecidableEq S] (j : ℕ) (s t : S) (w : ⋀[k]^(j+1) M) :
    basisContract b (j+1) s (basisWedgeOne b (j+1) t w) =
      (if s = t then w else 0) - basisWedgeOne b j t (basisContract b j s w) := by
  classical
  rw [basisWedgeOne, exteriorContract_wedgeOne]
  by_cases h : s = t
  · subst t
    simp [basisWedgeOne]
  · simp [basisWedgeOne, h, Module.Basis.coord_apply, b.repr_self, Finsupp.single_eq_of_ne h]

/-- 座標偏微分の和としての係数つき外冪の微分。 -/
def tensorExteriorD (D : S → A →ₗ[k] A) (j : ℕ) :
    (A ⊗[k] (⋀[k]^j M)) →ₗ[k] A ⊗[k] (⋀[k]^(j+1) M) :=
  ∑ s, TensorProduct.map (D s) (basisWedgeOne b j s)

/-- 一つの座標の積分と内部積で定めた次数を下げる作用素。 -/
def tensorExteriorH (I : A →ₗ[k] A) (s : S) (j : ℕ) :
    (A ⊗[k] (⋀[k]^(j+1) M)) →ₗ[k] A ⊗[k] (⋀[k]^j M) :=
  TensorProduct.map I (basisContract b j s)

/-- 正次数の外冪での微分と一座標の収縮の反交換子。 -/
theorem tensorExteriorD_H (D : S → A →ₗ[k] A) (I : A →ₗ[k] A) (s : S)
    (hc : ∀ t, t ≠ s → (D t).comp I = I.comp (D t)) (j : ℕ) :
    (tensorExteriorD b D j).comp (tensorExteriorH b I s j) +
      (tensorExteriorH b I s (j+1)).comp (tensorExteriorD b D (j+1)) =
      TensorProduct.map (I.comp (D s)) LinearMap.id +
        TensorProduct.map ((D s).comp I - I.comp (D s))
          ((basisWedgeOne b j s).comp (basisContract b j s)) := by
  classical
  apply TensorProduct.ext'
  intro f w
  simp only [tensorExteriorD, tensorExteriorH, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.sum_apply, TensorProduct.map_tmul, map_sum, LinearMap.id_apply, LinearMap.sub_apply]
  rw [← Finset.sum_add_distrib, Finset.sum_eq_single s]
  · rw [basisContract_wedgeOne, ite_eq_left rfl, TensorProduct.tmul_sub, TensorProduct.sub_tmul]
    abel
  · intro t _ hts
    rw [basisContract_wedgeOne, ite_eq_right (Ne.symm hts), zero_sub, TensorProduct.tmul_neg]
    have h := DFunLike.congr_fun (hc t hts) f
    change D t (I f) = I (D t f) at h
    rw [h, add_neg_cancel]
  · simp

/-- 零次では内部積と微分の合成は積分の後の偏微分で与えられる。 -/
theorem tensorExteriorH_D_zero (D : S → A →ₗ[k] A) (I : A →ₗ[k] A) (s : S) :
    (tensorExteriorH b I s 0).comp (tensorExteriorD b D 0) =
      TensorProduct.map (I.comp (D s)) LinearMap.id := by
  classical
  apply TensorProduct.ext'
  intro f w
  simp only [tensorExteriorH, tensorExteriorD, LinearMap.comp_apply, LinearMap.sum_apply,
    TensorProduct.map_tmul, map_sum, LinearMap.id_apply, basisWedgeOne,
    basisContract, exteriorContract_wedgeZero]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ ht
    simp [Module.Basis.coord_apply, Ne.symm ht]
  · simp

end SerrePositivity.DeRham
