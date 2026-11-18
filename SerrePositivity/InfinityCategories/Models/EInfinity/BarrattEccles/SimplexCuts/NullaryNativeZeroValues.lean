module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryNativeBalanceTerms
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryCanonicalBalanceValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.DegenerateCutGeneratorFamilies
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryZeroColor

/-!
模型。文献の定義との比較は後で
# 元の全空語添字における固定零項の値

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §373。
反復出現と退化raw語で消える元の項を、全Cutごとの値で保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- 同じ退化raw語に対応する元の全大Cut項はそれぞれ零（BF §2.2.6）。 -/
lemma nullaryOuterCutTerm_eq_zero_of_raw_degenerate
    (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (r + 1) (m + 2)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hv : ∀ i, k.succAbove (w i) = v.val (p.succAbove i)) (hw : ¬_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate w)
    (ν : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (x : S _⦋q⦌) (z : ℤ)
    (hz : -((m + q + 1 - r : ℕ) : ℤ) = z) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm A S v ν k x z hz s = 0 := by
  by_cases hzero : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v k = 0
  · unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm
    have hpoint := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_zero_hi_eq_lo s v k hzero p hp
    have hcut := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.not_nondegenerate_of_nullary_raw_degenerate s v w p k hpoint hv hw
    have ht : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S s v x) : ℤ) = z := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_cutGeneratorFamily]
      have h : (m + 1) + q + 1 - (r + 1) = m + q + 1 - r := by omega
      rwa [h]
    have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_cutGeneratorFamily_eq_zero A S s v x hcut z ht
    simp only [H, TensorProduct.tmul_zero, map_zero, smul_zero]
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm_eq_zero_of_nonzero A S v ν k x z hz s hzero

/-- 反復出現では元の全分割と全Cutの全項が零（BF §1.2.4・§2.2.6）。 -/
lemma nullaryNativeBalanceTerm_eq_zero_of_count_ne_one
    (A : Type u) [CommRing A] (S : SSet.{0}) {m d : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 2) d) (ν : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (q : ℕ) (hcount : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k ≠ 1)
    (i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryNativeBalanceIndex u k q) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeBalanceTerm A S u ν k q i x = 0 := by
  cases i with
  | inl c => exact False.elim (hcount c.1.count_eq_one_of_empty)
  | inr s =>
    change -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterTerm A S u ν k q s x = 0
    have H : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterTerm A S u ν k q s x = 0 := by
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm_eq_zero_of_nonzero
      intro hz
      have hc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_zero_occurrenceCount s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterWord u) k hz
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterWord_count] at hc
      exact hcount hc
    rw [H, neg_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
