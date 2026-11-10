module

public import SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# 多変数 Cartier の代表形式の基底

## 概要
多項式単項式と外積単項式の積で、全ての座標の重みが p の倍数になる代表を表す。

## 方針
一次形式がある座標の微分は外積の平方零で消える。他の座標では偏微分の係数が標数で消える。

## 規約
座標の重みは多項式の指数と、その座標の一次形式が現れるかどうかの和。

## 使われ方
有限多変数の inverse Cartier。
-/

public noncomputable section

open scoped TensorProduct
open MvPolynomial Set Set.powersetCard

universe u

namespace SerrePositivity.DeRham

variable (K T : Type u) [CommRing K] [Fintype T] [LinearOrder T]

/-- 多項式単項式と外積単項式のテンソル基底。 -/
def polynomialFormsBasis (j : ℕ) :
    Module.Basis ((T →₀ ℕ) × powersetCard T j) K (forms K T j) :=
  (basisMonomials T K).tensorProduct ((Pi.basisFun K T).exteriorPower j)

private theorem wedgeOne_basis_of_mem (j : ℕ) (s : powersetCard T j) (t : T) (ht : t ∈ s) :
    wedgeOne K (T → K) j ((exteriorPower.oneEquiv K (T → K)).symm (Pi.single t 1))
      ((Pi.basisFun K T).exteriorPower j s) = 0 := by
  let f := (Pi.basisFun K T) ∘ (ofFinEmbEquiv.symm s)
  obtain ⟨i, hi⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s t).mpr ht
  apply Subtype.ext
  simp only [wedgeOne_coe, exteriorPower.oneEquiv_symm_apply, exteriorPower.ιMulti_apply_coe,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe, Submodule.coe_zero]
  change ExteriorAlgebra.ιMulti K 1 (fun _ => Pi.single t 1) *
    ExteriorAlgebra.ιMulti K j f = 0
  have h : f i = Pi.single t (1 : K) := by
    change Pi.basisFun K T ((ofFinEmbEquiv.symm s) i) = _
    rw [hi, Pi.basisFun_apply]
  rw [← h, ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply]
  simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] using
    ExteriorAlgebra.ι_mul_prod_list (R := K) f i

/-- 各座標で p の倍数の重みを持つ単項式形式を判定する。 -/
def CartierWeight (p : ℕ) {j : ℕ} (m : T →₀ ℕ) (s : powersetCard T j) : Prop :=
  ∀ t : T, p ∣ m t + if t ∈ s.val then 1 else 0

omit [Fintype T] in
private theorem cast_exponent_zero (p : ℕ) (hp : (p : K) = 0)
    {j : ℕ} {m : T →₀ ℕ} {s : powersetCard T j}
    (h : CartierWeight T p m s) (t : T) (ht : t ∉ s) : (m t : K) = 0 := by
  have hd : p ∣ m t := by
    have ht' : t ∉ s.val := ht
    simpa [ht'] using h t
  obtain ⟨q, hq⟩ := hd
  rw [hq, Nat.cast_mul, hp, zero_mul]

/-- 全ての重みが p の倍数なら単項式形式は閉形式。 -/
theorem polynomialFormsBasis_cartier_closed (p : ℕ) (hp : (p : K) = 0)
    {j : ℕ} (m : T →₀ ℕ) (s : powersetCard T j) (h : CartierWeight T p m s) :
    deRhamD K T j (polynomialFormsBasis K T j (m,s)) = 0 := by
  rw [polynomialFormsBasis, Module.Basis.tensorProduct_apply', coe_basisMonomials]
  unfold deRhamD deRhamDLinear
  simp only [LinearMap.toAddMonoidHom_coe, LinearMap.sum_apply, TensorProduct.map_tmul,
    Derivation.coeFn_coe]
  apply Finset.sum_eq_zero
  intro t _
  by_cases ht : t ∈ s
  · rw [wedgeOne_basis_of_mem K T j s t ht, TensorProduct.tmul_zero]
  · rw [pderiv_monomial, cast_exponent_zero K T p hp h t ht, mul_zero, map_zero,
      TensorProduct.zero_tmul]

private def supportIndicator {j : ℕ} (s : powersetCard T j) : T →₀ ℕ :=
  Finsupp.onFinset s.val (fun t => if t ∈ s.val then 1 else 0) (by aesop)

/-- 元の単項式の指数に、Cartier 代表の指数を対応させる。 -/
def cartierExponent (p : ℕ) {j : ℕ} (m : T →₀ ℕ) (s : powersetCard T j) : T →₀ ℕ :=
  p • m + (p-1) • supportIndicator T s

omit [Fintype T] in
private theorem cartierExponent_apply (p : ℕ) {j : ℕ} (m : T →₀ ℕ)
    (s : powersetCard T j) (t : T) :
    cartierExponent T p m s t = p * m t + (p-1) * (if t ∈ s.val then 1 else 0) := by
  simp [cartierExponent, supportIndicator, nsmul_eq_mul]

omit [Fintype T] in
/-- Cartier 代表の全ての重みは p の倍数。 -/
theorem cartierExponent_weight (p : ℕ) (hp : 0 < p) {j : ℕ} (m : T →₀ ℕ)
    (s : powersetCard T j) : CartierWeight T p (cartierExponent T p m s) s := by
  intro t
  rw [cartierExponent_apply]
  by_cases ht : t ∈ s.val
  · rw [ite_eq_left ht, mul_one, Nat.add_assoc, Nat.sub_add_cancel hp]
    exact dvd_add (dvd_mul_right _ _) (dvd_refl _)
  · simp [ht]

private def cartierExponentRoot (p : ℕ) (m : T →₀ ℕ) : T →₀ ℕ :=
  Finsupp.mapRange (fun n => n / p) (Nat.zero_div p) m

omit [Fintype T] in
private theorem cartierExponentRoot_cartierExponent (p : ℕ) (hp : 0 < p) {j : ℕ}
    (m : T →₀ ℕ) (s : powersetCard T j) :
    cartierExponentRoot T p (cartierExponent T p m s) = m := by
  ext t
  change (cartierExponent T p m s t) / p = m t
  rw [cartierExponent_apply, Nat.mul_add_div hp]
  have h : (p-1) * (if t ∈ s.val then 1 else 0) < p := by
    split_ifs <;> omega
  rw [Nat.div_eq_of_lt h, add_zero]

omit [Fintype T] in
private theorem cartierExponent_cartierExponentRoot (p : ℕ) (hp : 0 < p) {j : ℕ}
    (m : T →₀ ℕ) (s : powersetCard T j) (h : CartierWeight T p m s) :
    cartierExponent T p (cartierExponentRoot T p m) s = m := by
  ext t
  have ht := h t
  rw [cartierExponent_apply]
  change p * (m t / p) + (p-1) * (if t ∈ s.val then 1 else 0) = m t
  by_cases hs : t ∈ s.val
  · rw [ite_eq_left hs, mul_one]
    rw [ite_eq_left hs] at ht
    obtain ⟨a, ha⟩ := ht
    have ha' : a ≠ 0 := by intro he; subst a; simp at ha
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha'
    have he : m t = p * a + (p-1) := by
      rw [Nat.mul_succ] at ha
      omega
    rw [he, Nat.mul_add_div hp, Nat.div_eq_of_lt (by omega : p-1 < p), add_zero]
  · rw [ite_eq_right hs, mul_zero, add_zero]
    rw [ite_eq_right hs, add_zero] at ht
    exact Nat.mul_div_cancel' ht

/-- 元の単項式と、Cartier 重みを満たす単項式の全単射。 -/
def cartierMonomialEquiv (p : ℕ) (hp : 0 < p) (j : ℕ) :
    ((T →₀ ℕ) × powersetCard T j) ≃
      { ms : (T →₀ ℕ) × powersetCard T j // CartierWeight T p ms.1 ms.2 } where
  toFun ms := ⟨(cartierExponent T p ms.1 ms.2, ms.2), cartierExponent_weight T p hp ms.1 ms.2⟩
  invFun ms := (cartierExponentRoot T p ms.1.1, ms.1.2)
  left_inv ms := Prod.ext (cartierExponentRoot_cartierExponent T p hp ms.1 ms.2) rfl
  right_inv ms := Subtype.ext (Prod.ext (cartierExponent_cartierExponentRoot T p hp _ _ ms.2) rfl)

end SerrePositivity.DeRham
