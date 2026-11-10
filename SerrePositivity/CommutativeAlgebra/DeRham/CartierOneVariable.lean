module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# 一変数の Cartier 係数計算

## 概要
一変数多項式の微分の核と余核を、指数の p による剰余で表す。

## 方針
核は指数を p 倍する展開で、余核は指数が p−1 に合同な係数の抽出で記述する。

## 規約
定数体の係数は固定する。

## 使われ方
有限多項式の inverse Cartier。
-/

public noncomputable section

universe u

namespace SerrePositivity.DeRham

open Polynomial

variable (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

local notation "P" => Polynomial K

private theorem prime_pos : 0 < p := (Fact.out : Nat.Prime p).pos

private theorem prime_ne_zero : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero

omit [CharP K p] in
private theorem extract_coeff (f : P) (n : ℕ) :
    ((contract p (X * f)).divX).coeff n = f.coeff ((n + 1) * p - 1) := by
  rw [coeff_divX, coeff_contract (prime_ne_zero p)]
  have h : 0 < (n+1)*p := Nat.mul_pos (Nat.succ_pos n) (prime_pos p)
  have e : (n+1)*p-1+1 = (n+1)*p := Nat.sub_add_cancel h
  rw [← e, coeff_X_mul, Nat.add_sub_cancel]

/-- 指数が p−1 に合同な係数を抽出する。 -/
def polynomialCartierExtract : P →ₗ[K] P where
  toFun f := (contract p (X * f)).divX
  map_add' f g := by ext n; simp only [extract_coeff K p, coeff_add]
  map_smul' a f := by
    ext n
    simp only [RingHom.id_apply, extract_coeff K p, coeff_smul]

omit [CharP K p] in
private theorem polynomialCartierExtract_coeff (f : P) (n : ℕ) :
    (polynomialCartierExtract K p f).coeff n = f.coeff ((n+1)*p-1) :=
  extract_coeff K p f n

/-- Cartier 一次類の代表は、指数を p 倍した後に X の p−1 乗を掛ける。 -/
def polynomialCartierRepresentative : P →ₗ[K] P where
  toFun f := X^(p-1) * expand K p f
  map_add' f g := by simp [map_add, mul_add]
  map_smul' a f := by simp [Algebra.mul_smul_comm]

omit [CharP K p] in
/-- Cartier の係数抽出は指定した一次代表を戻す。 -/
theorem polynomialCartierExtract_representative (f : P) :
    polynomialCartierExtract K p (polynomialCartierRepresentative K p f) = f := by
  ext n
  rw [polynomialCartierExtract_coeff K p]
  change (X^(p-1) * expand K p f).coeff ((n+1)*p-1) = f.coeff n
  have e : (n+1)*p-1 = n*p + (p-1) := by
    rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_assoc (prime_pos p)]
  rw [e, coeff_X_pow_mul, coeff_expand_mul (prime_pos p)]

private theorem polynomialCartierExtract_derivative (f : P) :
    polynomialCartierExtract K p (derivative f) = 0 := by
  ext n
  have h : ((n+1)*p-1).succ = (n+1)*p :=
    Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos _) (prime_pos p))
  rw [polynomialCartierExtract_coeff K p, coeff_derivative, ← Nat.cast_succ, h, Nat.cast_mul,
    CharP.cast_eq_zero K p]
  simp

private def polynomialCartierPrimitive (f : P) : P :=
  ∑ n ∈ f.support, monomial (n+1) (f.coeff n / (n+1 : ℕ))

private theorem polynomialCartierPrimitive_derivative (f : P)
    (hf : polynomialCartierExtract K p f = 0) :
    derivative (polynomialCartierPrimitive K f) = f := by
  ext n
  simp only [polynomialCartierPrimitive, map_sum, derivative_monomial_succ, finsetSum_coeff,
    coeff_monomial, Finset.sum_ite_eq']
  by_cases hn : n ∈ f.support
  · rw [ite_eq_left hn, ← Nat.cast_succ]
    by_cases h : ((n+1 : ℕ) : K) = 0
    · rw [h, mul_zero]
      obtain ⟨m, hm⟩ := (CharP.cast_eq_zero_iff K p _).mp h
      have hm' : m ≠ 0 := by rintro rfl; simp at hm
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm'
      have he := congrArg (fun g : P => g.coeff i) hf
      rw [polynomialCartierExtract_coeff K p, coeff_zero, Nat.mul_comm (i+1), ← hm,
        Nat.add_sub_cancel] at he
      exact he.symm
    · exact div_mul_cancel₀ _ h
  · rw [ite_eq_right hn]
    exact (notMem_support_iff.mp hn).symm

/-- 微分の像は Cartier 係数抽出の核。 -/
theorem polynomialCartierExtract_ker :
    (polynomialCartierExtract K p).ker = (derivative (R := K)).range := by
  ext f
  constructor
  · intro hf
    exact ⟨polynomialCartierPrimitive K f, polynomialCartierPrimitive_derivative K p f hf⟩
  · rintro ⟨g, rfl⟩
    exact polynomialCartierExtract_derivative K p g

/-- 一変数微分の余核を Cartier 係数で表す。 -/
def polynomialCartierCokernel : (P ⧸ (derivative (R := K)).range) ≃ₗ[K] P :=
  (Submodule.quotEquivOfEq _ _ (polynomialCartierExtract_ker K p).symm).trans
    ((polynomialCartierExtract K p).quotKerEquivOfSurjective
      (fun f => ⟨polynomialCartierRepresentative K p f,
        polynomialCartierExtract_representative K p f⟩))

/-- 一変数微分の核は指数を p 倍して得られる。 -/
def polynomialCartierKernel : P ≃ₗ[K] (derivative (R := K)).ker := by
  let f := (expand K p).toLinearMap.codRestrict (derivative (R := K)).ker (fun a => by
    change derivative (expand K p a) = 0
    rw [derivative_expand]
    have hp : (p : P) = 0 := by
      rw [← map_natCast (C : K →+* P), CharP.cast_eq_zero K p, map_zero]
    rw [hp, zero_mul, mul_zero])
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    exact expand_injective (prime_pos p) (congrArg Subtype.val hab)
  · intro a
    exact ⟨contract p a.1, Subtype.ext (expand_contract p a.2 (prime_ne_zero p))⟩

end SerrePositivity.DeRham
