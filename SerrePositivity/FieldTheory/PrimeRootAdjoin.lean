module

public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.CharP.Lemmas

/-! # 一つの p 乗根の添加

概要：標数 `p` の体の拡大 `K/F` で、`x ∉ F` かつ `x^p = a ∈ F` とする。このとき
- `a` は `F` の中で p 乗でない。
- `x` の最小多項式は `X^p - a`。
- `1, x, …, x^{p-1}` は `F` 上独立で、`[F(x) : F] = p`。
方針：`a` が p 乗でないことと Mathlib の `X_pow_sub_C_irreducible_of_prime` から既約性を得て、
最小多項式を決める。次数と独立性は最小多項式の次数から読む。
規約：底体 `F` は任意の体で、p 乗部分体に限らない。
使われ方：p 独立族の拡張（`PIndependentSet`）、p 乗根の添加での微分の延長と次元
（`PAdjoinDerivation`・`PrimeRootDifferentialRank`）、p 乗部分体の族の交わり（`PrimeRootPowerSubfield`）。
-/

@[expose] public section
namespace SerrePositivity
open Polynomial

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- 底体の外のp乗根の係数は、底体の中ではp乗にならない。 -/
theorem primeRoot_coefficient_not_pow
    (x : K) (a : F) (hpow : x ^ p = algebraMap F K a)
    (hx : x ∉ Set.range (algebraMap F K)) (y : F) : y ^ p ≠ a := by
  intro hy
  have heq : (algebraMap F K y) ^ p = x ^ p := by
    rw [← map_pow, hy, hpow]
  exact hx ⟨y, (frobenius_inj K p) heq⟩

/-- p 乗が基礎体に属すが元自体は属さない場合の最小多項式。 -/
theorem minpoly_eq_X_pow_sub_C_of_pow_eq
    (x : K) (a : F) (hpow : x ^ p = algebraMap F K a)
    (hx : x ∉ Set.range (algebraMap F K)) :
    minpoly F x = X ^ p - C a := by
  have hirr : Irreducible (X ^ p - C a) := by
    apply X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime)
    exact primeRoot_coefficient_not_pow x a hpow hx
  apply (minpoly.eq_of_irreducible_of_monic hirr ?_
    (monic_X_pow_sub_C a (Fact.out : p.Prime).ne_zero)).symm
  simp [hpow]

omit [CharP K p] in
/-- この一段の添加は実際に整拡大である。 -/
theorem isIntegral_of_prime_pow_eq (x : K) (a : F)
    (hpow : x ^ p = algebraMap F K a) : IsIntegral F x := by
  refine ⟨X ^ p - C a, monic_X_pow_sub_C a (Fact.out : p.Prime).ne_zero, ?_⟩
  simp [hpow]

/-- 添加する元の p 未満の冪は既存体上で独立。 -/
theorem linearIndependent_pow_of_prime_pow_eq
    (x : K) (a : F) (hpow : x ^ p = algebraMap F K a)
    (hx : x ∉ Set.range (algebraMap F K)) :
    LinearIndependent F (fun i : Fin p ↦ x ^ (i : ℕ)) := by
  have h := linearIndependent_pow (K := F) x
  rwa [minpoly_eq_X_pow_sub_C_of_pow_eq x a hpow hx, natDegree_X_pow_sub_C] at h

/-- 既存体の外の一つの p 乗根を添加した次数はちょうど p。 -/
theorem finrank_adjoin_of_prime_pow_eq
    (x : K) (a : F) (hpow : x ^ p = algebraMap F K a)
    (hx : x ∉ Set.range (algebraMap F K)) :
    Module.finrank F (IntermediateField.adjoin F {x}) = p := by
  rw [(IntermediateField.adjoin.powerBasis (isIntegral_of_prime_pow_eq x a hpow)).finrank]
  simp [minpoly_eq_X_pow_sub_C_of_pow_eq x a hpow hx]

end SerrePositivity
