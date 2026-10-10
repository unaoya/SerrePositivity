module

public import SerrePositivity.CategoryTheory.ConeLengthBinomial
public import Mathlib.Algebra.FiniteSupport.Basic

/-! # 上に有界な係数列に対する反復錐の消去

二項変換 `(1 + shift)^e` は、十分高い cochain 次数で消える係数列の上で単射。
下側の有界性は不要なので、無限射影分解のホモロジーにも適用できる。
有界性なしでは交代列が `1 + shift` の核になるため、この仮定は省けない。
-/

@[expose] public section

namespace SerrePositivity

/-- 一段の零射の錐の係数から、上に有界な元の係数列を復元できる。 -/
lemma coneLength_cancel (f g : ℤ → ℝ) (a : ℤ)
    (hf : ∀ q, a ≤ q → f q = 0) (hg : ∀ q, a ≤ q → g q = 0)
    (h : (cochainLengthShift + 1) f = (cochainLengthShift + 1) g) : f = g := by
  funext q
  by_cases hq : a ≤ q
  · rw [hf q hq, hg q hq]
  · apply Int.leInductionDown (motive := fun q _ ↦ f q = g q)
      ((hf a le_rfl).trans (hg a le_rfl).symm) ?_ q (by omega)
    intro k _ hk
    have he := congrFun h (k - 1)
    simp only [LinearMap.add_apply, cochainLengthShift_apply, Module.End.one_apply,
      Pi.add_apply, sub_add_cancel] at he
    linarith

/-- 反復錐の係数列も同じ上限より上では消える。 -/
lemma coneLength_pow_eq_zero_above (n : ℕ) (f : ℤ → ℝ) (a : ℤ)
    (hf : ∀ q, a ≤ q → f q = 0) (q : ℤ) (hq : a ≤ q) :
    ((cochainLengthShift + 1) ^ n) f q = 0 := by
  induction n generalizing q with
  | zero => simpa using hf q hq
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    simp only [LinearMap.add_apply, cochainLengthShift_apply, Module.End.one_apply,
      Pi.add_apply, ih q hq, ih (q + 1) (by omega), add_zero]

/-- 任意回数の反復錐の係数が一致すれば、上に有界な元の係数も一致する。 -/
lemma coneLength_pow_cancel (n : ℕ) (f g : ℤ → ℝ) (a : ℤ)
    (hf : ∀ q, a ≤ q → f q = 0) (hg : ∀ q, a ≤ q → g q = 0)
    (h : ((cochainLengthShift + 1) ^ n) f = ((cochainLengthShift + 1) ^ n) g) :
    f = g := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply] at h
    exact ih (coneLength_cancel _ _ a
      (coneLength_pow_eq_zero_above n f a hf)
      (coneLength_pow_eq_zero_above n g a hg) h)

/-- 二項係数公式を両側で確認すれば、各次数の評価が一意に決まる。 -/
theorem coneLength_binomial_cancel (n : ℕ) (f g : ℤ → ℝ) (a : ℤ)
    (hf : ∀ q, a ≤ q → f q = 0) (hg : ∀ q, a ≤ q → g q = 0)
    (h : ∀ q, (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * f (q + j)) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * g (q + j)) : f = g := by
  apply coneLength_pow_cancel n f g a hf hg
  funext q
  simpa only [coneLength_binomial] using h q

/-- 有限支持の評価と上に有界な極限列は、二項変換の一致から同定できる。 -/
theorem coneLength_binomial_cancel_of_hasFiniteSupport (n : ℕ) (f g : ℤ → ℝ)
    (hf : Function.HasFiniteSupport f) (a : ℤ) (hg : ∀ q, a ≤ q → g q = 0)
    (h : ∀ q, (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * f (q + j)) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * g (q + j)) : f = g := by
  obtain ⟨b, hb⟩ := hf.bddAbove
  apply coneLength_binomial_cancel n f g (max a (b + 1)) ?_ ?_ h
  · intro q hq
    by_contra hn
    have := hb (show q ∈ Function.support f from hn)
    omega
  · intro q hq
    exact hg q (le_trans (le_max_left _ _) hq)

/-- 有限支持の二つの係数列について、同じ回数の零錐を消去できる。 -/
theorem coneLength_pow_cancel_of_hasFiniteSupport (n : ℕ) (f g : ℤ → ℝ)
    (hf : Function.HasFiniteSupport f) (hg : Function.HasFiniteSupport g)
    (h : ((cochainLengthShift + 1) ^ n) f = ((cochainLengthShift + 1) ^ n) g) : f = g := by
  obtain ⟨b, hb⟩ := hg.bddAbove
  apply coneLength_binomial_cancel_of_hasFiniteSupport n f g hf (b + 1) ?_ ?_
  · intro q hq
    by_contra hn
    have := hb (show q ∈ Function.support g from hn)
    omega
  · intro q
    simpa only [coneLength_binomial] using congrFun h q

end SerrePositivity
