module

public import SerrePositivity.HomologicalAlgebra.Tor
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Serre の交点重複度 `χ^R(M, N)`

## 概要

Serre の交点重複度 `χ^R(M, N) = Σ_i (-1)^i ℓ_R(Tor_i^R(M, N))` を定義する。`Tor_i^R(M, N)` は
Mathlib の `Tor` を加群とみた `TorModule R i M N`、その長さは `torLength R i M N`
（`HomologicalAlgebra/Tor.lean`）。論文の主定理（`Paper/Statement.lean`）は、正則局所環 `R` と
素イデアル `P`、`Q` で `R/P ⊗ R/Q` が有限長かつ `dim R/P + dim R/Q = dim R` なるものについて
`χ^R(R/P, R/Q) > 0` を主張する。

## 規約（`notes/PLAN.md` §1.4）

和は `finsum` で、値は整数。長さが無限なら `ENat.toNat` で `0`、非零項が無限個なら `finsum` は `0` を
返す。正則局所環上の有限生成加群では `Tor_i = 0 (i > dim R)` なので有限和になるが、これはここでは
示さず、必要な場面で `chi_eq_sum_range` の仮定として受け取る。`Tor` が有限長であることも定義には
含めない。
-/

@[expose] public section

universe u

namespace SerrePositivity

variable (R : Type u) [CommRing R]
variable (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Serre の交点重複度 `χ^R(M, N) = Σ_i (-1)^i ℓ_R(Tor_i^R(M, N))`（整数値）。無限長の項は `0` と
数え、非零項が無限個なら `0`。 -/
noncomputable def chi : ℤ :=
  ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * ((torLength R i M N).toNat : ℤ)

/-- `i > n` で `ℓ(Tor_i) = 0` なら、`χ^R(M, N)` は `i = 0, …, n` の通常の有限和に等しい（`finsum` の台が
`{0, …, n}` に入る）。`Tor` が `dim R` より上で消えることと組み合わせて使う。 -/
lemma chi_eq_sum_range (n : ℕ) (h : ∀ i, n < i → torLength R i M N = 0) :
    chi R M N = ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * ((torLength R i M N).toNat : ℤ) := by
  unfold chi
  apply finsum_eq_sum_of_support_subset
  intro i hi
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hn
  exact hi (by simp [h i (by omega)])

end SerrePositivity
