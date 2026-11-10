module

public import SerrePositivity.CommutativeAlgebra.DeRham.CartierWeight
public import SerrePositivity.CommutativeAlgebra.DeRham.CartierCoordinateHomotopy
import all SerrePositivity.CommutativeAlgebra.DeRham.Polynomial
import all SerrePositivity.CommutativeAlgebra.DeRham.ExteriorCoordinateProjection
import all SerrePositivity.CommutativeAlgebra.DeRham.ExteriorTensorContraction
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierWeight

/-!
# Cartier 射影の単項式基底上の表示

## 概要
一座標の Cartier 射影は、その座標の重みが p の倍数なら単項式を保ち、それ以外を零に送る。

## 方針
指定の一次形式を含むかで外冪の座標射影の値を計算する。

## 規約
各座標の重みは、多項式の指数と外積での出現回数の和。

## 使われ方
すべての座標を合わせた Cartier 射影。
-/

public noncomputable section

open CategoryTheory MvPolynomial Set Set.powersetCard
open scoped TensorProduct

universe u

namespace SerrePositivity.DeRham

variable (K T : Type u) [Field K] [Fintype T] [LinearOrder T]

local notation "b" => Pi.basisFun K T

private theorem vectorProjection_basis (s t : T) :
    exteriorCoordinateProjection ((b).coord s) (b s) (b t) =
      if t = s then 0 else b t := by
  unfold exteriorCoordinateProjection
  rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs with h
  · subst t
    simp
  · simp

private theorem exteriorProjection_basis (j : ℕ) (s : T) (S : powersetCard T j) :
    exteriorPower.map j (exteriorCoordinateProjection ((b).coord s) (b s))
      ((b).exteriorPower j S) = if s ∈ S.val then 0 else (b).exteriorPower j S := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti]
  by_cases h : s ∈ S.val
  · rw [ite_eq_left h]
    obtain ⟨i, hi⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem S s).mpr h
    apply (exteriorPower.ιMulti K j).map_coord_zero (i := i)
    change exteriorCoordinateProjection ((b).coord s) (b s) (b (ofFinEmbEquiv.symm S i)) = 0
    rw [hi, vectorProjection_basis, ite_eq_left rfl]
  · rw [ite_eq_right h]
    congr 1
    funext i
    have hi : (ofFinEmbEquiv.symm S) i ≠ s :=
      fun he => h ((mem_range_ofFinEmbEquiv_symm_iff_mem S s).mp ⟨i, he⟩)
    change exteriorCoordinateProjection ((b).coord s) (b s) (b (ofFinEmbEquiv.symm S i)) = _
    rw [vectorProjection_basis, ite_eq_right hi]
    rfl

private theorem contractWedge_basis (j : ℕ) (s : T) (S : powersetCard T (j + 1)) :
    ((basisWedgeOne b j s).comp (basisContract b j s)) ((b).exteriorPower (j + 1) S) =
      if s ∈ S.val then (b).exteriorPower (j + 1) S else 0 := by
  have h := DFunLike.congr_fun (exteriorPower_map_coordinateProjection ((b).coord s) (b s) j)
    ((b).exteriorPower (j + 1) S)
  rw [exteriorProjection_basis] at h
  change (if s ∈ S.val then 0 else (b).exteriorPower (j + 1) S) =
    (b).exteriorPower (j + 1) S -
      ((basisWedgeOne b j s).comp (basisContract b j s)) ((b).exteriorPower (j + 1) S) at h
  split_ifs at h ⊢
  · exact (sub_eq_zero.mp h.symm).symm
  · exact sub_eq_self.mp h.symm

variable (p : ℕ) [CharP K p]

set_option backward.isDefEq.respectTransparency false in
/-- 一座標の Cartier 射影は、その座標で重みが p の倍数の基底元を残す。 -/
theorem cartierCoordinateEval_basis (j : ℕ) (s : T) (m : T →₀ ℕ) (S : powersetCard T j) :
    (cartierCoordinateEval K T s).f j (polynomialFormsBasis K T j (m, S)) =
      if p ∣ m s + (if s ∈ S.val then 1 else 0) then polynomialFormsBasis K T j (m, S) else 0 := by
  cases j with
  | zero =>
    rw [cartierCoordinateEval_zero, polynomialFormsBasis, Module.Basis.tensorProduct_apply',
      coe_basisMonomials]
    have hs : s ∉ S.val := by
      have he : S.val.card = 0 := S.prop
      simp [Finset.card_eq_zero.mp he]
    change TensorProduct.map (cartierCoordinateProjection K s 0) LinearMap.id
      (monomial m 1 ⊗ₜ[K] (b).exteriorPower 0 S) = _
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, cartierCoordinateProjection_monomial,
      Nat.add_zero, CharP.cast_eq_zero_iff K p, hs, ite_false]
    split_ifs <;> simp
  | succ j =>
    rw [cartierCoordinateEval_succ, polynomialFormsBasis, Module.Basis.tensorProduct_apply',
      coe_basisMonomials]
    change (TensorProduct.map (cartierCoordinateProjection K s 0)
        (exteriorPower.map (j + 1) (exteriorCoordinateProjection ((b).coord s) (b s))) +
      TensorProduct.map (cartierCoordinateProjection K s 1)
        ((basisWedgeOne b j s).comp (basisContract b j s)))
      (monomial m 1 ⊗ₜ[K] (b).exteriorPower (j + 1) S) = _
    simp only [LinearMap.add_apply, TensorProduct.map_tmul, exteriorProjection_basis, contractWedge_basis,
      cartierCoordinateProjection_monomial, Nat.add_zero, CharP.cast_eq_zero_iff K p]
    by_cases hs : s ∈ S.val <;> simp only [hs, ite_true, ite_false,
      TensorProduct.tmul_zero, zero_add, add_zero] <;> split_ifs <;> simp

end SerrePositivity.DeRham
