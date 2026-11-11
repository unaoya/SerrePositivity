module
public import Mathlib.Algebra.Ring.NegOnePow

/-!
概要：一次面列の符号を外側の次元符号と通常の交代面符号へ分ける。
方針：整数の negOnePow の加法則と自然数冪の比較を使う。
規約：実加法群上の作用として示す。
使われ方：一次作用素の各列の有限交代和への分解。
-/
@[expose] public section
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

lemma dgCoherentBarFirstFaceSign (n i : ℕ) {M : Type*} [AddCommGroup M] (z : M) :
    ((n : ℤ) + 1 + (i : ℤ) + 1).negOnePow • z =
      (-1 : ℤ) ^ (i + 1) • (((n : ℤ) + 1).negOnePow • z) := by
  have h : (n : ℤ) + 1 + (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) + ((n : ℤ) + 1) := by omega
  rw [h, Int.negOnePow_add]
  simp only [Units.smul_def, Units.val_mul, smul_smul, Int.coe_negOnePow_natCast]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
