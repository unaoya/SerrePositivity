module

public import SerrePositivity.EInfinity.SimplexCuts.RemainingSegmentCrossInversions
public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentIntervalLengths
public import SerrePositivity.EInfinity.SimplexCuts.RemainingCaesuraWeights

/-!
# 元の一部分語にわたる交差和と成分次数の補正

Berger–Fresse §1.2.5・§2.2.4・§2.2.6、M14 L12a の C452。
同じ交差寄与を部分語の外へ出し、元の区間長の総和で畳む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ部分語の交差和は、元の外側区間長と成分次数で畳める（BF §2.2.6）。 -/
lemma positiveComposite_segment_cross_intervalLength_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k)
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    (∑ z : Fin (c.1.val i).val,
      (IntervalCuts.positionInversionTerm (positiveCompositeCutWord u v k c.1).val
          (compositeFirstPosition u v k c.1 p) (positiveCompositeSegmentPosition u v k c.1 i z) +
        IntervalCuts.positionInversionTerm (positiveCompositeCutWord u v k c.1).val
          (positiveCompositeSegmentPosition u v k c.1 i z) (compositeFirstPosition u v k c.1 p)) *
      intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
        (compositeFirstPosition u v k c.1 p) *
      intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
        (positiveCompositeSegmentPosition u v k c.1 i z)) =
    (IntervalCuts.positionInversionTerm (positiveWord u).val p (positiveOccurrencePosition u k i) +
      IntervalCuts.positionInversionTerm (positiveWord u).val
        (positiveOccurrencePosition u k i) p) *
      intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p *
      (intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val
        (positiveOccurrencePosition u k i) + Surjection.segmentDegree v.val c.1 i) := by
  simp_rw [positiveComposite_remaining_segment_cross_inversionTerm u v k c.1 p hp i,
    positiveComposite_remaining_intervalLength u v k c p hp]
  rw [← Finset.mul_sum, positiveComposite_segment_intervalLength_sum]

end SerrePositivity.EInfinity.SimplexCuts
