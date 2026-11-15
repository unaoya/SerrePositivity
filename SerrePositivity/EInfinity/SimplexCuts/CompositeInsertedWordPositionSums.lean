module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeRemainingWordPositionSums
public import SerrePositivity.EInfinity.SimplexCuts.CompositeWordPositionSums
public import SerrePositivity.EInfinity.SimplexCuts.InsertionColorSumDecomposition

/-!
# 元の挿入色の全位置の和

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の C452。
同じ全位置の二分解の残り位置の和を消去し、既存の部分語の位置へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 挿入色の全出現の和は、同じ全部分語の位置の和（BF §2.2.6）。 -/
lemma positiveComposite_inserted_wordPosition_sum {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (F : Fin (m + n + (d + e) + 1) → ℕ) :
    (∑ b : Fin (n + 1),
      ∑ h : ↥(Surjection.occurrences (positiveCompositeCutWord u v k r).val
        (BarrattEccles.insertedPosition m (n + 1) k b)), F h.val) =
      ∑ i : Fin (Surjection.occurrenceCount u.val k), ∑ z : Fin (r.val i).val,
        F (positiveCompositeSegmentPosition u v k r i z) := by
  have h := sum_occurrences (positiveCompositeCutWord u v k r).val F
  rw [sum_insertion_positions m (n + 1) k] at h
  rw [positiveComposite_remaining_wordPosition_sum u v k r F,
    positiveComposite_wordPosition_sum u v k r F] at h
  exact Nat.add_left_cancel h

end SerrePositivity.EInfinity.SimplexCuts
