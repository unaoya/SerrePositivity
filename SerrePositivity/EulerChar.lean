module

public import SerrePositivity.Tor
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Serre の交点重複度 `χ^R(M, N)`

`χ^R(M, N) = Σ_i (-1)^i length_R Tor_i^R(M, N)` を `finsum` で定義する。

junk value（`notes/PLAN.md` §1.4）：長さが無限なら `ENat.toNat` で `0`、
非零項が無限個なら `finsum` の値は `0`。正則局所環上の有限生成加群では
`Tor_i = 0 (i > dim R)` なので有限和になる（これは層 3a の事実で、ここでは示さない）。
-/

@[expose] public section

universe u

namespace SerrePositivity

variable (R : Type u) [CommRing R]
variable (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Serre の交点重複度 `χ^R(M, N) = Σ_i (-1)^i length_R Tor_i^R(M, N)`。 -/
noncomputable def chi : ℤ :=
  ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * ((torLength R i M N).toNat : ℤ)

/-- `Tor_i` の長さが `i > n` で `0` なら、`χ` は `i ≤ n` の有限和に等しい。 -/
lemma chi_eq_sum_range (n : ℕ) (h : ∀ i, n < i → torLength R i M N = 0) :
    chi R M N = ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * ((torLength R i M N).toNat : ℤ) := by
  unfold chi
  apply finsum_eq_sum_of_support_subset
  intro i hi
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hn
  exact hi (by simp [h i (by omega)])

end SerrePositivity
