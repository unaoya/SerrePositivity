module

public import SerrePositivity.EInfinity.SimplexCuts.RemainingSegmentOrder
public import SerrePositivity.EInfinity.SimplexCuts.CompositeRemainingPositions
public import SerrePositivity.EInfinity.IntervalCuts.PivotPositionOrder
public import SerrePositivity.EInfinity.IntervalCuts.NonpivotPositionOrder
public import SerrePositivity.EInfinity.IntervalCuts.InversionCounts

/-!
# 残り位置と同じ挿入部分語の交差逆転寄与

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
両方向の位置順序と色順序を、元の外側位置と指定色の出現へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ残り位置と部分語の両向き交差寄与は、元の外側の寄与（BF §2.2.6）。 -/
lemma positiveComposite_remaining_segment_cross_inversionTerm {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    IntervalCuts.positionInversionTerm (positiveCompositeCutWord u v k r).val
        (compositeFirstPosition u v k r p) (positiveCompositeSegmentPosition u v k r i z) +
      IntervalCuts.positionInversionTerm (positiveCompositeCutWord u v k r).val
        (positiveCompositeSegmentPosition u v k r i z) (compositeFirstPosition u v k r p) =
    IntervalCuts.positionInversionTerm (positiveWord u).val p (positiveOccurrencePosition u k i) +
      IntervalCuts.positionInversionTerm (positiveWord u).val
        (positiveOccurrencePosition u k i) p := by
  simp only [IntervalCuts.positionInversionTerm,
    (positiveComposite_remaining_segment_order u v k r p hp i z).1,
    (positiveComposite_remaining_segment_order u v k r p hp i z).2,
    positiveCompositeFirstPosition_label u v k r p hp,
    positiveCompositeSegmentPosition_label,
    IntervalCuts.insertedPosition_lt_remaining_iff,
    IntervalCuts.remainingPosition_lt_inserted_iff, positiveOccurrencePosition_value]

end SerrePositivity.EInfinity.SimplexCuts
