module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveComponentDifferential

/-!
模型。文献の定義との比較は後で
# 切断双線形成分の全整数 Leibniz 則

Berger–Fresse §2.2.7、M14 L10 の証明分割。
零次数を含む同じ二つの微分像を、全整数の元の複体で比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- C315：同じ次数の等式で Leibniz の各次数を指定した形に戻す。 -/
lemma positiveIntegerBilinear_d_reindex (S : SSet.{0}) (n : ℕ)
    (i j i' j' t t' : ℤ) (hi : i' = i + 1) (hj : j' = j + 1)
    (ht : t = i + j) (ht' : t' = i + j + 1)
    (a : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (n + 1)).X i) (b : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X j)
    (H : (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (n + 1)).d t t'
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S n i j t (by omega) a b) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S n i' j t' (by omega)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (n + 1)).d i i' a) b +
      i.negOnePow • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S n i j' t' (by omega) a
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).d j j' b)) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (n + 1)).d (i + j) (i + j + 1)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S n i j (i + j) rfl a b) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S n (i + 1) j (i + j + 1) (by omega)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (n + 1)).d i (i + 1) a) b +
      i.negOnePow • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S n i (j + 1) (i + j + 1) (by omega) a
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).d j (j + 1) b) := by
  subst i'
  subst j'
  subst t
  subst t'
  exact H

/-- C306：正 arity の同じ双線形成分の、全整数での Leibniz 則。 -/
lemma positiveIntegerBilinear_d (S : SSet.{0}) (r : ℕ) (i j : ℤ)
    (a : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (r + 1)).X i) (b : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X j) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).d (i + j) (i + j + 1)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S r i j (i + j) rfl a b) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S r (i + 1) j (i + j + 1) (by omega)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (r + 1)).d i (i + 1) a) b +
      i.negOnePow • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear A S r i (j + 1) (i + j + 1) (by omega) a
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).d j (j + 1) b) := by
  by_cases hi : 0 < i
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex_eq_zero_of_positive A (r + 1) i hi a]
    simp
  by_cases hj : 0 < j
  · have hb : b = 0 := by
      let _ : Subsingleton ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X j) := ModuleCat.isZero_iff_subsingleton.mp
        (_root_.SerrePositivity.NegativeTensor.isZero_positive (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A S) j hj)
      exact Subsingleton.elim _ _
    rw [hb]
    simp
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, i = -(d : ℤ) := ⟨(-i).toNat, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
  cases d with
  | zero =>
    cases q with
    | zero =>
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_d_reindex A S r _ _ 1 1
        (-((0 + 0 : ℕ) : ℤ)) (-((0 + 0 : ℕ) : ℤ) + 1)
        (by omega) (by omega) (by omega) (by omega) a b
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_neg A S r 0 0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_eq_zero_left A S r 1 _ _ _
        (by omega), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_eq_zero_right A S r _ 1 _ _ (by omega)]
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedCoefficientBoundary, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedSimplexBoundary,
        LinearMap.zero_apply, smul_zero, zero_add] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComponent_d A S r 0 0 a b
    | succ q =>
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_d_reindex A S r _ _ 1 (-(q : ℤ))
        (-((0 + (q + 1) : ℕ) : ℤ)) (-((0 + (q + 1) : ℕ) : ℤ) + 1)
        (by omega) (by omega) (by omega) (by omega) a b
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_neg, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_eq_zero_left A S r 1 _ _ _
        (by omega)]
      have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComponent_d A S r 0 (q + 1) a b
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveSimplexBoundary_succ] at H
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedCoefficientBoundary, LinearMap.zero_apply, zero_add,
        Nat.cast_zero, neg_zero, Int.negOnePow_zero, one_smul, pow_zero] using H
  | succ d =>
    cases q with
    | zero =>
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_d_reindex A S r _ _ (-(d : ℤ)) 1
        (-(((d + 1) + 0 : ℕ) : ℤ)) (-(((d + 1) + 0 : ℕ) : ℤ) + 1)
        (by omega) (by omega) (by omega) (by omega) a b
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_neg, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_eq_zero_right A S r _ 1 _ _
        (by omega)]
      have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComponent_d A S r (d + 1) 0 a b
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCoefficientBoundary_succ] at H
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedSimplexBoundary, LinearMap.zero_apply, smul_zero, add_zero] using H
    | succ q =>
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_d_reindex A S r _ _ (-(d : ℤ)) (-(q : ℤ))
        (-(((d + 1) + (q + 1) : ℕ) : ℤ)) (-(((d + 1) + (q + 1) : ℕ) : ℤ) + 1)
        (by omega) (by omega) (by omega) (by omega) a b
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveIntegerBilinear_neg]
      have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComponent_d A S r (d + 1) (q + 1) a b
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCoefficientBoundary_succ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveSimplexBoundary_succ] at H
      simpa only [Int.negOnePow_neg, Units.smul_def, Int.coe_negOnePow_natCast] using H

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
