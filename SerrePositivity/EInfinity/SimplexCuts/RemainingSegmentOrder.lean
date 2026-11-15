module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentPositions
public import SerrePositivity.EInfinity.SimplexCuts.CompositeFirstPositionOrder
public import SerrePositivity.EInfinity.SimplexCuts.PositiveOccurrencePosition

/-!
# 元の残り位置と挿入部分語の位置の前後

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の C452。
異なる接頭ブロックの順序を保ち、部分語内の相対位置によらない前後を読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の残り位置と部分語内の位置の順序は、元の外側の前後（BF §2.2.6）。 -/
lemma positiveComposite_remaining_segment_order {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    (compositeFirstPosition u v k r p < positiveCompositeSegmentPosition u v k r i z ↔
      p < positiveOccurrencePosition u k i) ∧
    (positiveCompositeSegmentPosition u v k r i z < compositeFirstPosition u v k r p ↔
      positiveOccurrencePosition u k i < p) := by
  have hne : p ≠ positiveOccurrencePosition u k i := by
    intro he
    exact hp ((congrArg (positiveWord u).val he).trans (positiveOccurrencePosition_value u k i))
  rcases lt_or_gt_of_ne hne with h | h
  · have hn : compositeFirstPosition u v k r p <
        positiveCompositeSegmentPosition u v k r i z := by
      have hh := compositeFirstPosition_strictMono u v k r h
      change compositePrefixLength u v k r p.val <
        compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val at hh
      change compositePrefixLength u v k r p.val <
        compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val + z.val
      omega
    exact ⟨⟨fun _ => h, fun _ => hn⟩,
      ⟨fun hd => False.elim (lt_asymm hn hd), fun hd => False.elim (lt_asymm h hd)⟩⟩
  · have hn : positiveCompositeSegmentPosition u v k r i z <
        compositeFirstPosition u v k r p := by
      have hval : (Surjection.occurrenceAt u.val k i).val < p.val := h
      have hm := compositePrefixLength_monotone u v k r
        (show (Surjection.occurrenceAt u.val k i).val + 1 ≤ p.val by omega)
      have hs := IntervalCuts.substitute_prefix_length_at_occurrence u v k r i
      change compositePrefixLength u v k r ((Surjection.occurrenceAt u.val k i).val + 1) =
        compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val + (r.val i).val at hs
      rw [hs] at hm
      change compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val + z.val <
        compositePrefixLength u v k r p.val
      have hz := z.isLt
      omega
    exact ⟨⟨fun hd => False.elim (lt_asymm hn hd), fun hd => False.elim (lt_asymm h hd)⟩,
      ⟨fun _ => h, fun _ => hn⟩⟩

end SerrePositivity.EInfinity.SimplexCuts
