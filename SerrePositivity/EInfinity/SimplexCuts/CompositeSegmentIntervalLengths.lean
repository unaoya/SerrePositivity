module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentIntervalWidths
public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentCaesuraCounts

/-!
# 元の挿入部分語の区間長の総和

Berger–Fresse §1.2.5・§2.2.4・§2.2.6、M14 L12a の C452。
同じ幾何学的な幅と同じ区切り数の和を、元の外側区間長と成分次数へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ部分語の全区間長は元の外側区間長と成分次数の和（BF §2.2.6）。 -/
lemma positiveComposite_segment_intervalLength_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    (∑ z : Fin (c.1.val i).val,
      intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
        (positiveCompositeSegmentPosition u v k c.1 i z)) =
      intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val
        (positiveOccurrencePosition u k i) + Surjection.segmentDegree v.val c.1 i := by
  have hw := positiveComposite_segment_intervalWidth_sum u v k c i
  have hc := positiveComposite_segment_caesura_sum u v k c.1 i
  unfold intervalLength
  rw [Finset.sum_add_distrib, hc]
  omega

end SerrePositivity.EInfinity.SimplexCuts
