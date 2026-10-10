module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval

/-! # Euler 評価に共通する交代和の添字変換

環や複体に依存しない、整数添字の平行移動と自然数添字への取り直し。
有限支持でない場合も `finsum` の規約と両立する。
-/

@[expose] public section

namespace SerrePositivity

/-- 整数添字の交代和を一つずらすと符号が反転する。 -/
lemma alternatingFinsum_sub_one (f : ℤ → ℝ) :
    (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * f (i - 1)) =
      -(∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * f i) := by
  calc
    _ = ∑ᶠ i : ℤ, (((i + 1).negOnePow : ℤ) : ℝ) * f i := by
      have h := finsum_comp_equiv (Equiv.addRight (1 : ℤ))
        (f := fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * f (i - 1))
      simpa using h.symm
    _ = ∑ᶠ i : ℤ, -(((i.negOnePow : ℤ) : ℝ) * f i) := by
      congr 1
      funext i
      simp [Int.negOnePow_add]
    _ = _ := finsum_neg_distrib _

/-- 正の添字で `0` になる実数列 `a : ℤ → ℝ` について、交代和 `Σ_{i ∈ ℤ} (-1)^i a_i` は
`Σ_{n ∈ ℕ} (-1)^n a_{-n}` に等しい。`finsum` の台が `{-n}` に含まれることと、単射 `n ↦ -n` に沿った
`finsum` の取り直し（`finsum_mem_range`）による。有限台を仮定せず、`finsum` の規約による値も含めて
成り立つ。 -/
lemma alternating_finsum_eq_nat (a : ℤ → ℝ) (hpos : ∀ i, 0 < i → a i = 0) :
    (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * a i) =
      ∑ᶠ n : ℕ, (-1 : ℝ) ^ n * a (-(n : ℤ)) := by
  let f := fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * a i
  let g := fun i : ℕ ↦ -(i : ℤ)
  have hg : Function.Injective g := by
    intro i j hij
    dsimp [g] at hij
    exact_mod_cast neg_injective hij
  have hs : Function.support f ⊆ Set.range g := by
    intro i hi
    have hnonpos : i ≤ 0 := by
      by_contra hn
      exact hi (by simp [f, hpos i (by omega)])
    refine ⟨(-i).toNat, ?_⟩
    dsimp [g]
    rw [Int.toNat_of_nonneg (by omega), neg_neg]
  have hfull : (∑ᶠ i ∈ Set.range g, f i) = ∑ᶠ i : ℤ, f i := by
    rw [← finsum_mem_inter_support f (Set.range g), Set.inter_eq_right.mpr hs,
      finsum_mem_support]
  change (∑ᶠ i : ℤ, f i) = _
  rw [← hfull, finsum_mem_range hg]
  simp only [f, g, Int.negOnePow_neg, Int.cast_negOnePow_natCast]

end SerrePositivity
