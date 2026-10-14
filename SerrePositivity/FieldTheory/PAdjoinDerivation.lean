module

public import SerrePositivity.FieldTheory.PAdjoin
public import SerrePositivity.FieldTheory.PowerBasisDerivation
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Adjoin.PowerBasis

/-! # 一段の p 乗根添加の導分

既約な `X^p-a` の微分が零であることを証明し、添加した元を1に送る導分を構成する。
-/

@[expose] public section
namespace SerrePositivity
open Polynomial

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- 一段の p 乗根添加の最小多項式は微分が零。 -/
theorem derivative_minpoly_eq_zero_of_prime_pow_eq
    (x : K) (a : F) (hpow : x ^ p = algebraMap F K a)
    (hx : x ∉ Set.range (algebraMap F K)) : derivative (minpoly F x) = 0 := by
  let : CharP F p := (algebraMap F K).charP (algebraMap F K).injective p
  rw [minpoly_eq_X_pow_sub_C_of_pow_eq x a hpow hx]
  simp [derivative_X_pow]

/-- 一段の添加の実際の体上に、添加元を1に送る導分が存在する。 -/
theorem exists_derivation_adjoin_primeRoot
    (x : K) (a : F) (hpow : x ^ p = algebraMap F K a)
    (hx : x ∉ Set.range (algebraMap F K)) :
    ∃ δ : Derivation F (IntermediateField.adjoin F {x}) (IntermediateField.adjoin F {x}),
      δ (IntermediateField.AdjoinSimple.gen F x) = 1 := by
  let B := IntermediateField.adjoin.powerBasis (isIntegral_of_prime_pow_eq x a hpow)
  have hzero : derivative (minpoly F B.gen) = 0 := by
    rw [show minpoly F B.gen = minpoly F x by
      simp only [B, IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]]
    exact derivative_minpoly_eq_zero_of_prime_pow_eq x a hpow hx
  refine ⟨B.generatorDerivation hzero, ?_⟩
  exact B.generatorDerivation_gen hzero

/-- 一つの p 乗根が終域全体を生成する場合は、終域自身に導分を供給する。 -/
theorem exists_derivation_primeRoot_of_adjoin_eq_top
    (x : K) (a : F) (hpow : x ^ p = algebraMap F K a)
    (hx : x ∉ Set.range (algebraMap F K)) (hs : Algebra.adjoin F {x} = ⊤) :
    ∃ δ : Derivation F K K, δ x = 1 := by
  let B := PowerBasis.ofAdjoinEqTop (isIntegral_of_prime_pow_eq x a hpow) hs
  have hgen : B.gen = x := PowerBasis.ofAdjoinEqTop_gen _ _
  have hzero : derivative (minpoly F B.gen) = 0 := by
    rw [hgen]
    exact derivative_minpoly_eq_zero_of_prime_pow_eq x a hpow hx
  refine ⟨B.generatorDerivation hzero, ?_⟩
  rw [← hgen]
  exact B.generatorDerivation_gen hzero

end SerrePositivity
