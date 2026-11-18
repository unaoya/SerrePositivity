module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeInsertedWordPositionSums

/-!
模型。文献の定義との比較は後で
# 元の残り位置と部分語位置にわたる交差和の再添字付け

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の C452。
同じ二種類の位置の和を二変数へ適用し、両方向の交差和を戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 残り色から挿入色への全対の和を、同じ位置対へ戻す（BF §2.2.6）。 -/
lemma positiveComposite_remaining_inserted_wordPosition_sum {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (F : Fin (m + n + (d + e) + 1) → Fin (m + n + (d + e) + 1) → ℕ) :
    (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : Fin (n + 1),
      ∑ p : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
        (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m (n + 1) k a)),
      ∑ h : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
        (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m (n + 1) k b)), F p.val h.val) =
    ∑ p : {p : Fin (m + d + 1) // (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p ≠ k},
      ∑ i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k), ∑ z : Fin (r.val i).val,
        F (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeFirstPosition u v k r p.val)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k r i z) := by
  calc
    _ = ∑ a : {a : Fin (m + 1) // a ≠ k},
        ∑ p : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
          (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m (n + 1) k a)),
        ∑ b : Fin (n + 1),
        ∑ h : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
          (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m (n + 1) k b)), F p.val h.val := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ a : {a : Fin (m + 1) // a ≠ k},
        ∑ p : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
          (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m (n + 1) k a)),
        ∑ i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k), ∑ z : Fin (r.val i).val,
          F p.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k r i z) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro p _
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComposite_inserted_wordPosition_sum u v k r (F p.val)
    _ = _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComposite_remaining_wordPosition_sum u v k r
      (fun p => ∑ i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k), ∑ z : Fin (r.val i).val,
        F p (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k r i z))

/-- 挿入色から残り色への全対の和も、同じ位置対へ戻す（BF §2.2.6）。 -/
lemma positiveComposite_inserted_remaining_wordPosition_sum {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (F : Fin (m + n + (d + e) + 1) → Fin (m + n + (d + e) + 1) → ℕ) :
    (∑ a : Fin (n + 1), ∑ b : {b : Fin (m + 1) // b ≠ k},
      ∑ p : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
        (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m (n + 1) k a)),
      ∑ h : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
        (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m (n + 1) k b)), F p.val h.val) =
    ∑ h : {h : Fin (m + d + 1) // (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val h ≠ k},
      ∑ i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k), ∑ z : Fin (r.val i).val,
        F (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k r i z)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeFirstPosition u v k r h.val) := by
  calc
    _ = ∑ b : {b : Fin (m + 1) // b ≠ k}, ∑ a : Fin (n + 1),
        ∑ h : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
          (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m (n + 1) k b)),
        ∑ p : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
          (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m (n + 1) k a)), F p.val h.val := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveComposite_remaining_inserted_wordPosition_sum u v k r
      (fun h p => F p h)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
