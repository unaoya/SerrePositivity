module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryNativeBalanceTerms
public import SerrePositivity.EInfinity.SimplexCuts.NullaryCanonicalBalanceValues
public import SerrePositivity.EInfinity.SimplexCuts.DegenerateCutGeneratorFamilies
public import SerrePositivity.EInfinity.SimplexCuts.NullaryZeroColor

/-!
# 元の全空語添字における固定零項の値

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §373。
反復出現と退化raw語で消える元の項を、全Cutごとの値で保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial

/-- 同じ退化raw語に対応する元の全大Cut項はそれぞれ零（BF §2.2.6）。 -/
lemma nullaryOuterCutTerm_eq_zero_of_raw_degenerate
    (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (v : Surjection.Word (r + 1) (m + 2)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hv : ∀ i, k.succAbove (w i) = v.val (p.succAbove i)) (hw : ¬Surjection.Nondegenerate w)
    (ν : Surjection.BasisWord 0 0) (x : S _⦋q⦌) (z : ℤ)
    (hz : -((m + q + 1 - r : ℕ) : ℤ) = z) (s : Cut (m + 1) q) :
    nullaryOuterCutTerm A S v ν k x z hz s = 0 := by
  by_cases hzero : outputDegree s v k = 0
  · unfold nullaryOuterCutTerm
    have hpoint := outputDegree_zero_hi_eq_lo s v k hzero p hp
    have hcut := not_nondegenerate_of_nullary_raw_degenerate s v w p k hpoint hv hw
    have ht : -(vectorDegree (chains A S) (r + 1) (cutGeneratorFamily A S s v x) : ℤ) = z := by
      rw [vectorDegree_cutGeneratorFamily]
      have h : (m + 1) + q + 1 - (r + 1) = m + q + 1 - r := by omega
      rwa [h]
    have H := vectorTensorAt_cutGeneratorFamily_eq_zero A S s v x hcut z ht
    simp only [H, TensorProduct.tmul_zero, map_zero, smul_zero]
  · exact nullaryOuterCutTerm_eq_zero_of_nonzero A S v ν k x z hz s hzero

/-- 反復出現では元の全分割と全Cutの全項が零（BF §1.2.4・§2.2.6）。 -/
lemma nullaryNativeBalanceTerm_eq_zero_of_count_ne_one
    (A : Type u) [CommRing A] (S : SSet.{0}) {m d : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (q : ℕ) (hcount : Surjection.occurrenceCount u.val k ≠ 1)
    (i : NullaryNativeBalanceIndex u k q) (x : S _⦋q⦌) :
    nullaryNativeBalanceTerm A S u ν k q i x = 0 := by
  cases i with
  | inl c => exact False.elim (hcount c.1.count_eq_one_of_empty)
  | inr s =>
    change -nullaryNativeOuterTerm A S u ν k q s x = 0
    have H : nullaryNativeOuterTerm A S u ν k q s x = 0 := by
      apply nullaryOuterCutTerm_eq_zero_of_nonzero
      intro hz
      have hc := outputDegree_zero_occurrenceCount s (nullaryNativeOuterWord u) k hz
      rw [nullaryNativeOuterWord_count] at hc
      exact hcount hc
    rw [H, neg_zero]

end SerrePositivity.EInfinity.SimplexCuts
