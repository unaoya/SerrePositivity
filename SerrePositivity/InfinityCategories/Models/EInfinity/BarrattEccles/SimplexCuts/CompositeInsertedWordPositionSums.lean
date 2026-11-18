module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeRemainingWordPositionSums
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeWordPositionSums
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.InsertionColorSumDecomposition

/-!
模型。文献の定義との比較は後で
# 元の挿入色の全位置の和

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の C452。
同じ全位置の二分解の残り位置の和を消去し、既存の部分語の位置へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 挿入色の全出現の和は、同じ全部分語の位置の和（BF §2.2.6）。 -/
lemma positiveComposite_inserted_wordPosition_sum {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (F : Fin (m + n + (d + e) + 1) → ℕ) :
    (∑ b : Fin (n + 1),
      ∑ h : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
        (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m (n + 1) k b)), F h.val) =
      ∑ i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k), ∑ z : Fin (r.val i).val,
        F (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k r i z) := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val F
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_insertion_positions m (n + 1) k] at h
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComposite_remaining_wordPosition_sum u v k r F,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComposite_wordPosition_sum u v k r F] at h
  exact Nat.add_left_cancel h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
