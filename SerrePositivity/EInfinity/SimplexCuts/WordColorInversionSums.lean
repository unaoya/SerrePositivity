module

public import SerrePositivity.EInfinity.SimplexCuts.OccurrenceFiberSums
public import SerrePositivity.EInfinity.SimplexCuts.Signs

/-!
# 元の逆転指数の色別の出現位置の有限和

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
既存の同じ重み付き逆転指数を、元の色の fiber へまとめる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の逆転指数は、同じ全色対の出現位置ごとの和（BF §2.2.4）。 -/
lemma permutationExponent_eq_sum_occurrence_pairs {m q r : ℕ} (s : Cut m q)
    (w : Fin (m + 1) → Fin r) :
    permutationExponent s w =
    ∑ a : Fin r, ∑ b : Fin r,
      ∑ p : ↥(Surjection.occurrences w a), ∑ h : ↥(Surjection.occurrences w b),
      if p.val < h.val ∧ w h.val < w p.val then
        intervalLength s w p.val * intervalLength s w h.val else 0 := by
  symm
  calc
    _ = ∑ a : Fin r, ∑ p : ↥(Surjection.occurrences w a),
        ∑ b : Fin r, ∑ h : ↥(Surjection.occurrences w b),
        if p.val < h.val ∧ w h.val < w p.val then
          intervalLength s w p.val * intervalLength s w h.val else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ a : Fin r, ∑ p : ↥(Surjection.occurrences w a), ∑ h : Fin (m + 1),
        if p.val < h ∧ w h < w p.val then
          intervalLength s w p.val * intervalLength s w h else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro p _
      exact sum_occurrences w (fun h => if p.val < h ∧ w h < w p.val then
        intervalLength s w p.val * intervalLength s w h else 0)
    _ = ∑ p : Fin (m + 1), ∑ h : Fin (m + 1),
        if p < h ∧ w h < w p then intervalLength s w p * intervalLength s w h else 0 :=
      sum_occurrences w (fun p => ∑ h : Fin (m + 1),
        if p < h ∧ w h < w p then intervalLength s w p * intervalLength s w h else 0)
    _ = _ := rfl

end SerrePositivity.EInfinity.SimplexCuts
