module

public import SerrePositivity.FieldTheory.PMonomialSpan
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.RingTheory.AlgebraTower

/-! # 一つの p 乗根の添加

既存体に属さない元で p 乗が既存体に属するなら、最小多項式は
`X^p - a`、添加の次数は p。p 独立族の拡張のための一段の補題。
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

theorem minpoly_natDegree_of_pow_eq
    (x : K) (a : F) (hpow : x ^ p = algebraMap F K a)
    (hx : x ∉ Set.range (algebraMap F K)) : (minpoly F x).natDegree = p := by
  rw [minpoly_eq_X_pow_sub_C_of_pow_eq x a hpow hx, natDegree_X_pow_sub_C]

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
  have hdeg := minpoly_natDegree_of_pow_eq (p := p) x a hpow hx
  rw [hdeg] at h
  exact h

/-- 既存体の外の一つの p 乗根を添加した次数はちょうど p。 -/
theorem finrank_adjoin_of_prime_pow_eq
    (x : K) (a : F) (hpow : x ^ p = algebraMap F K a)
    (hx : x ∉ Set.range (algebraMap F K)) :
    Module.finrank F (IntermediateField.adjoin F {x}) = p := by
  rw [(IntermediateField.adjoin.powerBasis (isIntegral_of_prime_pow_eq x a hpow)).finrank]
  exact minpoly_natDegree_of_pow_eq x a hpow hx

/-- p 乗部分体を含む任意の中間体について、一段の冪の独立性を供給する。 -/
theorem linearIndependent_pow_over_pIntermediateField
    (E : IntermediateField (pPowerSubfield K p) K) (x : K) (hx : x ∉ E) :
    LinearIndependent E (fun i : Fin p ↦ x ^ (i : ℕ)) := by
  let a : E := ⟨x ^ p, E.algebraMap_mem
    ⟨x ^ p, (mem_pPowerSubfield K p _).mpr ⟨x, rfl⟩⟩⟩
  apply linearIndependent_pow_of_prime_pow_eq x a rfl
  rintro ⟨y, hy⟩
  exact hx (hy ▸ y.property)

/-- p 乗部分体を含む中間体の外の元を添加した次数。 -/
theorem finrank_adjoin_over_pIntermediateField
    (E : IntermediateField (pPowerSubfield K p) K) (x : K) (hx : x ∉ E) :
    Module.finrank E (IntermediateField.adjoin E {x}) = p := by
  let a : E := ⟨x ^ p, E.algebraMap_mem
    ⟨x ^ p, (mem_pPowerSubfield K p _).mpr ⟨x, rfl⟩⟩⟩
  apply finrank_adjoin_of_prime_pow_eq x a rfl
  rintro ⟨y, hy⟩
  exact hx (hy ▸ y.property)

/-- 独立な単項式族に中間体の外の元を添加すると、単項式と p 未満の冪の積が独立。
元の族の添字が無限でも、Mathlib のスカラー塔の独立性から従う。 -/
theorem linearIndependent_pMonomial_mul_pow
    {ι : Type*} (b : ι → K)
    (hb : LinearIndependent (pPowerSubfield K p) (pMonomial (p := p) b))
    (x : K) (hx : x ∉ pMonomialIntermediateField (p := p) b) :
    LinearIndependent (pPowerSubfield K p)
      (fun i : PExponent p ι × Fin p ↦ pMonomial b i.1 * x ^ (i.2 : ℕ)) := by
  let E := pMonomialIntermediateField (p := p) b
  let v : PExponent p ι → E := fun d ↦
    ⟨pMonomial b d, Submodule.subset_span ⟨d, rfl⟩⟩
  have hbE : LinearIndependent (pPowerSubfield K p) v := by
    exact linearIndependent_span hb
  have h := linearIndependent_smul hbE (linearIndependent_pow_over_pIntermediateField E x hx)
  exact h

/-- 単項式が独立な族に、その生成する中間体の外の元を一つ添加しても独立。 -/
theorem linearIndependent_pMonomial_optionElim
    {ι : Type*} (b : ι → K)
    (hb : LinearIndependent (pPowerSubfield K p) (pMonomial (p := p) b))
    (x : K) (hx : x ∉ pMonomialIntermediateField (p := p) b) :
    LinearIndependent (pPowerSubfield K p) (pMonomial (p := p) (Option.elim' x b)) := by
  have h := (linearIndependent_pMonomial_mul_pow b hb x hx).comp
    PExponent.splitOption PExponent.splitOption_injective
  change LinearIndependent (pPowerSubfield K p) (fun d ↦ pMonomial (Option.elim' x b) d)
  simpa only [Function.comp_def, pMonomial_optionElim] using h

end SerrePositivity
