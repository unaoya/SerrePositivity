module

public import SerrePositivity.Asymptotic.NormalizedLimit
public import SerrePositivity.PerfectComplex.Free.Euler

/-!
# 一様有界な複体列の Euler 和と超極限

列の全項に共通する有限支持を使い、Euler の有限和と正規化超極限を交換する。
各段ごとの有界性だけではこの交換は主張しない。
ここでの対象は実際の複体列であり、支持つき商圏全体への評価の延長とは区別する。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter Asymptotics
open scoped BigOperators

/-- 共通の有限支持をもつ実数列の族では、有限支持和と超極限を交換できる。 -/
lemma normalizedLimit_finsum (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ℕ → ℕ) (hs : ∀ n, 0 < s n) {ι : Type*} (I : Finset ι) (f : ι → ℕ → ℝ)
    (hsupp : ∀ n i, i ∉ I → f i n = 0)
    (hf : ∀ i ∈ I, f i =O[atTop] (fun n ↦ (s n : ℝ))) :
    normalizedLimit U s (fun n ↦ ∑ᶠ i, f i n) =
      ∑ᶠ i, normalizedLimit U s (f i) := by
  have hsum (n : ℕ) : (∑ᶠ i, f i n) = ∑ i ∈ I, f i n := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hn
    exact hi (hsupp n i hn)
  have hlim : (∑ᶠ i, normalizedLimit U s (f i)) =
      ∑ i ∈ I, normalizedLimit U s (f i) := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hn
    apply hi
    change normalizedLimit U s (f i) = 0
    have heq : f i = fun _ ↦ 0 := funext fun n ↦ hsupp n i hn
    rw [heq, normalizedLimit_zero]
  simp_rw [hsum, hlim]
  exact normalizedLimit_sum U hU s hs I f hf

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 共通の有限な項の支持から、同じ範囲でのホモロジーの長さの消滅が従う。 -/
lemma lengthHomology_zero_outside (P : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (I : Finset ℤ) (hP : ∀ n i, i ∉ I → IsZero ((P n).X i))
    (n : ℕ) (i : ℤ) (hi : i ∉ I) : lam.len ((P n).homology i) = 0 := by
  have := ModuleCat.subsingleton_of_isZero (isZero_homology_of_isZero_X (P n) i (hP n i hi))
  exact lam.len_eq_zero_of_subsingleton _

/-- 共通有限支持と各次数の長さの `O(s)` 評価から、Euler 値の列も `O(s)` となる。 -/
lemma lambdaEuler_isBigO (s : ℕ → ℕ)
    (P : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (I : Finset ℤ)
    (hP : ∀ n i, i ∉ I → IsZero ((P n).X i))
    (hbound : ∀ i, (fun n ↦ (lam.len ((P n).homology i)).toReal)
      =O[atTop] (fun n ↦ (s n : ℝ))) :
    (fun n ↦ lambdaEuler lam (P n)) =O[atTop] (fun n ↦ (s n : ℝ)) := by
  have heq (n : ℕ) : lambdaEuler lam (P n) =
      ∑ i ∈ I, ((i.negOnePow : ℤ) : ℝ) * (lam.len ((P n).homology i)).toReal := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hn
    apply hi
    simp only [lengthHomology_zero_outside lam P I hP n i hn, ENNReal.toReal_zero, mul_zero]
  simp_rw [heq]
  exact IsBigO.fun_sum (fun i _ ↦ (hbound i).const_mul_left _)

/-- 共通有界な複体列では、各段の Euler 評価の超極限は、次数別超極限の Euler 和に等しい。 -/
lemma normalizedLimit_lambdaEuler (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ℕ → ℕ) (hs : ∀ n, 0 < s n)
    (P : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (I : Finset ℤ)
    (hP : ∀ n i, i ∉ I → IsZero ((P n).X i))
    (hbound : ∀ i, (fun n ↦ (lam.len ((P n).homology i)).toReal)
      =O[atTop] (fun n ↦ (s n : ℝ))) :
    normalizedLimit U s (fun n ↦ lambdaEuler lam (P n)) =
      ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) *
        normalizedLimit U s (fun n ↦ (lam.len ((P n).homology i)).toReal) := by
  unfold lambdaEuler
  rw [normalizedLimit_finsum U hU s hs I _ (fun n i hi ↦ by
    rw [lengthHomology_zero_outside lam P I hP n i hi, ENNReal.toReal_zero, mul_zero])
    (fun i _ ↦ (hbound i).const_mul_left _)]
  congr 1
  funext i
  exact normalizedLimit_const_mul U hU s hs _ (hbound i) _

end SerrePositivity.Asymptotic
