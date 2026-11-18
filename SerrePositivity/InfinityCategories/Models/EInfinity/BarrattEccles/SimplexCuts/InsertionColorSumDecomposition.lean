module

public import SerrePositivity.EInfinity.BarrattEccles.PermutationCompositionValues
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
模型。文献の定義との比較は後で
# 挿入後の全色の和を同じ二種類の色へ分ける

Berger–Fresse §0.10・§2.2.6、M14 L12a の C452。
既存の operadInsertionEquiv を使い、元の有限和と色対の二重和を再添字付けする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 全色の和は、同じ残り色と挿入色の二つの和（BF §0.10・2.2.6）。 -/
lemma sum_insertion_positions (m n : ℕ) (k : Fin (m + 1)) (F : Fin (m + n) → ℕ) :
    (∑ a, F a) =
      (∑ a : {a : Fin (m + 1) // a ≠ k}, F (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k a)) +
      ∑ b : Fin n, F (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b) := by
  simpa only [Fintype.sum_sum_type, _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition,
    _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).symm.sum_comp F |>.symm

/-- 全色対の和を、元の二種類の色の四つの対へ分ける（BF §2.2.6）。 -/
lemma sum_insertion_position_pairs (m n : ℕ) (k : Fin (m + 1))
    (F : Fin (m + n) → Fin (m + n) → ℕ) :
    (∑ a, ∑ b, F a b) =
      (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : {b : Fin (m + 1) // b ≠ k},
        F (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k a) (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k b)) +
      (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : Fin n,
        F (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k a) (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b)) +
      (∑ a : Fin n, ∑ b : {b : Fin (m + 1) // b ≠ k},
        F (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k a) (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k b)) +
      (∑ a : Fin n, ∑ b : Fin n,
        F (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k a) (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b)) := by
  simp_rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_insertion_positions m n k, Finset.sum_add_distrib]
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
