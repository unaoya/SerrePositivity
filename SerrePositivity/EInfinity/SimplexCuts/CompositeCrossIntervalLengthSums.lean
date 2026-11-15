module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeCrossWordPositionSums
public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentCrossSum
public import SerrePositivity.EInfinity.SimplexCuts.WeightedWordInversionPairs

/-!
# 全交差和を元の外側位置と成分次数へ戻す

Berger–Fresse §1.2.5・§2.2.4・§2.2.6、M14 L12a の C452。
両方向の元の和を同じ位置対へ戻し、一部分語の区間長の和で畳む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 全色の交差和は元の残り位置と外側出現の重みの和（BF §2.2.6）。 -/
lemma positiveComposite_cross_intervalLength_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    let δ := positiveCompositeOuterCut u v k c
    let w := (positiveCompositeCutWord u v k c.1).val
    let uPos := (positiveWord u).val
    (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : Fin (n + 1),
      ∑ p : ↥(Surjection.occurrences w (BarrattEccles.remainingPosition m (n + 1) k a)),
      ∑ h : ↥(Surjection.occurrences w (BarrattEccles.insertedPosition m (n + 1) k b)),
      if p.val < h.val ∧ w h.val < w p.val then
        intervalLength c.2 w p.val * intervalLength c.2 w h.val else 0) +
    (∑ a : Fin (n + 1), ∑ b : {b : Fin (m + 1) // b ≠ k},
      ∑ p : ↥(Surjection.occurrences w (BarrattEccles.insertedPosition m (n + 1) k a)),
      ∑ h : ↥(Surjection.occurrences w (BarrattEccles.remainingPosition m (n + 1) k b)),
      if p.val < h.val ∧ w h.val < w p.val then
        intervalLength c.2 w p.val * intervalLength c.2 w h.val else 0) =
    ∑ p : {p : Fin (m + d + 1) // uPos p ≠ k},
      ∑ i : Fin (Surjection.occurrenceCount u.val k),
      (IntervalCuts.positionInversionTerm uPos p.val (positiveOccurrencePosition u k i) +
        IntervalCuts.positionInversionTerm uPos (positiveOccurrencePosition u k i) p.val) *
        intervalLength δ uPos p.val *
        (intervalLength δ uPos (positiveOccurrencePosition u k i) +
          Surjection.segmentDegree v.val c.1 i) := by
  dsimp only
  rw [positiveComposite_remaining_inserted_wordPosition_sum u v k c.1
    (fun p h => if p < h ∧ (positiveCompositeCutWord u v k c.1).val h <
        (positiveCompositeCutWord u v k c.1).val p then
      intervalLength c.2 (positiveCompositeCutWord u v k c.1).val p *
        intervalLength c.2 (positiveCompositeCutWord u v k c.1).val h else 0),
    positiveComposite_inserted_remaining_wordPosition_sum u v k c.1
    (fun p h => if p < h ∧ (positiveCompositeCutWord u v k c.1).val h <
        (positiveCompositeCutWord u v k c.1).val p then
      intervalLength c.2 (positiveCompositeCutWord u v k c.1).val p *
        intervalLength c.2 (positiveCompositeCutWord u v k c.1).val h else 0)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ z : Fin (c.1.val i).val,
        (IntervalCuts.positionInversionTerm (positiveCompositeCutWord u v k c.1).val
            (compositeFirstPosition u v k c.1 p.val)
            (positiveCompositeSegmentPosition u v k c.1 i z) +
          IntervalCuts.positionInversionTerm (positiveCompositeCutWord u v k c.1).val
            (positiveCompositeSegmentPosition u v k c.1 i z)
            (compositeFirstPosition u v k c.1 p.val)) *
        intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
          (compositeFirstPosition u v k c.1 p.val) *
        intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
          (positiveCompositeSegmentPosition u v k c.1 i z) := by
      apply Finset.sum_congr rfl
      intro z _
      exact weighted_word_inversionPair_eq c.2 (positiveCompositeCutWord u v k c.1).val _ _
    _ = _ := positiveComposite_segment_cross_intervalLength_sum u v k c p.val p.property i

end SerrePositivity.EInfinity.SimplexCuts
