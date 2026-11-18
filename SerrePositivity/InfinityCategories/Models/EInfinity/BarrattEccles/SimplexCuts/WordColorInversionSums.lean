module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.OccurrenceFiberSums
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Signs

/-!
模型。文献の定義との比較は後で
# 元の逆転指数の色別の出現位置の有限和

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
既存の同じ重み付き逆転指数を、元の色の fiber へまとめる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の逆転指数は、同じ全色対の出現位置ごとの和（BF §2.2.4）。 -/
lemma permutationExponent_eq_sum_occurrence_pairs {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (w : Fin (m + 1) → Fin r) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.permutationExponent s w =
    ∑ a : Fin r, ∑ b : Fin r,
      ∑ p : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences w a), ∑ h : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences w b),
      if p.val < h.val ∧ w h.val < w p.val then
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s w p.val * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s w h.val else 0 := by
  symm
  calc
    _ = ∑ a : Fin r, ∑ p : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences w a),
        ∑ b : Fin r, ∑ h : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences w b),
        if p.val < h.val ∧ w h.val < w p.val then
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s w p.val * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s w h.val else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ a : Fin r, ∑ p : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences w a), ∑ h : Fin (m + 1),
        if p.val < h ∧ w h < w p.val then
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s w p.val * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s w h else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro p _
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_occurrences w (fun h => if p.val < h ∧ w h < w p.val then
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s w p.val * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s w h else 0)
    _ = ∑ p : Fin (m + 1), ∑ h : Fin (m + 1),
        if p < h ∧ w h < w p then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s w p * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s w h else 0 :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_occurrences w (fun p => ∑ h : Fin (m + 1),
        if p < h ∧ w h < w p then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s w p * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalLength s w h else 0)
    _ = _ := rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
