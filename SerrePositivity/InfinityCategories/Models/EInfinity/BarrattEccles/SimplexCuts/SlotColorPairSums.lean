module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.InsertionColorSumDecomposition
public import SerrePositivity.EInfinity.BarrattEccles.PermutationUnit
public import Mathlib.Algebra.BigOperators.Fin

/-!
模型。文献の定義との比較は後で
# 元の全色対の和と指定色を含む対

Berger–Fresse §0.10・§2.2.6、M14 L12a の C452。
arity 1の同じ既存の挿入位置の分解で、指定色の対を分離する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 同じ全色対の和を、指定色以外と指定色を含む対へ分ける（BF §2.2.6）。 -/
lemma sum_position_pairs_with_slot (m : ℕ) (k : Fin (m + 1))
    (F : Fin (m + 1) → Fin (m + 1) → ℕ) :
    (∑ a, ∑ b, F a b) =
      (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : {b : Fin (m + 1) // b ≠ k}, F a.val b.val) +
      (∑ a : {a : Fin (m + 1) // a ≠ k}, F a.val k) +
      (∑ b : {b : Fin (m + 1) // b ≠ k}, F k b.val) + F k k := by
  have hr (a : {a : Fin (m + 1) // a ≠ k}) :
      _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m 1 k a = a.val :=
    _root_.SerrePositivity.EInfinity.BarrattEccles.insertionEquiv_one_symm_left m k a
  have hi (a : Fin 1) : _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m 1 k a = k := by
    have ha : a = 0 := Subsingleton.elim a 0
    subst a
    apply Fin.ext
    change k.val + 0 = k.val
    omega
  simpa only [hr, hi, Fin.sum_univ_one] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_insertion_position_pairs m 1 k F

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
