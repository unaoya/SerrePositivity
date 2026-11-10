module

public import SerrePositivity.CommutativeAlgebra.DeRham.CartierOneVariable
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# 多変数 Cartier 計算の座標積分

## 概要
一つの変数の指数を上げる積分と、標数で消える指数を残す射影を作る。

## 方針
単項式基底で定義し、同じ座標の偏微分との合成および他の座標との可換性を示す。

## 規約
指数の係数が零の場合、積分の係数も零とする。

## 使われ方
有限多変数 de Rham 複体の Cartier 収縮。
-/

public noncomputable section

open MvPolynomial
open scoped Classical

universe u v

namespace SerrePositivity.DeRham

variable {S : Type v} (K : Type u) [Field K]

/-- 微分の係数が非零なら逆数を掛けて指定した指数を上げる。 -/
def cartierCoordinateIntegral (s : S) : MvPolynomial S K →ₗ[K] MvPolynomial S K :=
  (basisMonomials S K).constr K fun m =>
    monomial (m + Finsupp.single s 1) ((m s + 1 : ℕ) : K)⁻¹

/-- 指定した指数（次数を一つ足す場合を含む）が係数環で消える単項式を残す。 -/
def cartierCoordinateProjection (s : S) (q : ℕ) : MvPolynomial S K →ₗ[K] MvPolynomial S K :=
  (basisMonomials S K).constr K fun m => if ((m s + q : ℕ) : K) = 0 then monomial m 1 else 0

@[simp]
theorem cartierCoordinateIntegral_monomial (s : S) (m : S →₀ ℕ) (c : K) :
    cartierCoordinateIntegral K s (monomial m c) =
      monomial (m + Finsupp.single s 1) (c * (((m s + 1 : ℕ) : K)⁻¹)) := by
  have h : monomial m c = c • basisMonomials S K m := by simp [coe_basisMonomials, smul_monomial]
  rw [h, map_smul, cartierCoordinateIntegral, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

@[simp]
theorem cartierCoordinateProjection_monomial (s : S) (q : ℕ) (m : S →₀ ℕ) (c : K) :
    cartierCoordinateProjection K s q (monomial m c) =
      if ((m s + q : ℕ) : K) = 0 then monomial m c else 0 := by
  have h : monomial m c = c • basisMonomials S K m := by simp [coe_basisMonomials, smul_monomial]
  rw [h, map_smul, cartierCoordinateProjection, Module.Basis.constr_basis]
  split_ifs <;> simp [coe_basisMonomials, smul_monomial]

/-- 微分と積分の合成は、一次形式の Cartier 射影を引いた恒等写像。 -/
theorem cartierCoordinatePartial_integral (s : S) :
    (pderiv (R := K) s).toLinearMap.comp (cartierCoordinateIntegral K s) =
      LinearMap.id - cartierCoordinateProjection K s 1 := by
  apply (basisMonomials S K).ext
  intro m
  simp only [coe_basisMonomials, LinearMap.comp_apply, Derivation.coeFn_coe, LinearMap.sub_apply,
    LinearMap.id_apply, cartierCoordinateIntegral_monomial, cartierCoordinateProjection_monomial,
    pderiv_monomial, one_mul, add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same]
  split_ifs with h
  · rw [h, mul_zero, map_zero, sub_self]
  · rw [inv_mul_cancel₀ h, sub_zero]

/-- 積分と微分の合成は、零次形式の Cartier 射影を引いた恒等写像。 -/
theorem cartierCoordinateIntegral_partial (s : S) :
    (cartierCoordinateIntegral K s).comp (pderiv (R := K) s).toLinearMap =
      LinearMap.id - cartierCoordinateProjection K s 0 := by
  apply (basisMonomials S K).ext
  intro m
  simp only [coe_basisMonomials, LinearMap.comp_apply, Derivation.coeFn_coe, LinearMap.sub_apply,
    LinearMap.id_apply, cartierCoordinateProjection_monomial, pderiv_monomial, one_mul, Nat.add_zero]
  by_cases h : (m s : K) = 0
  · simp [h]
  · have hm : 0 < m s := Nat.pos_of_ne_zero fun e => h (by simp [e])
    have he : Finsupp.single s (1 : ℕ) ≤ m := by
      intro t
      by_cases ht : t = s
      · subst t
        simpa only [Finsupp.single_eq_same] using (show 1 ≤ m s by omega)
      · simp [Finsupp.single_eq_of_ne ht]
    rw [cartierCoordinateIntegral_monomial, tsub_add_cancel_of_le he, ite_eq_right h, sub_zero]
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    rw [Nat.sub_add_cancel hm, mul_inv_cancel₀ h]

/-- 他の変数の偏微分と座標積分は可換。 -/
theorem cartierCoordinatePartial_integral_comm {s t : S} (hst : s ≠ t) :
    (pderiv (R := K) t).toLinearMap.comp (cartierCoordinateIntegral K s) =
      (cartierCoordinateIntegral K s).comp (pderiv (R := K) t).toLinearMap := by
  apply (basisMonomials S K).ext
  intro m
  simp only [coe_basisMonomials, LinearMap.comp_apply, Derivation.coeFn_coe,
    cartierCoordinateIntegral_monomial, pderiv_monomial, one_mul, Finsupp.add_apply,
    Finsupp.single_eq_of_ne (Ne.symm hst), Finsupp.tsub_apply, Finsupp.single_eq_of_ne hst,
    add_zero, tsub_zero]
  have he : m + Finsupp.single s 1 - Finsupp.single t 1 =
      m - Finsupp.single t 1 + Finsupp.single s 1 := by
    ext a
    by_cases ha : a = t
    · subst a
      simp [Finsupp.single_eq_of_ne (Ne.symm hst)]
    · simp [Finsupp.single_eq_of_ne ha]
  rw [he, mul_comm]

end SerrePositivity.DeRham
