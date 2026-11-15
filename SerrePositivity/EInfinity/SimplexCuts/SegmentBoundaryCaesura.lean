module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSlotBoundary
public import SerrePositivity.EInfinity.SimplexCuts.SegmentWordPositions

/-!
# 元の共有端点による挿入色の区切り

Berger–Fresse §1.2.2・§1.2.4・§2.2.4、M14 L12a のC452。
元の隣接部分語の同じラベルを使い、最後の出現以外の共有端点を区切りとして読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の次の部分語との共有端点は、合成語の元の区切り（BF §2.2.4）。 -/
lemma positiveCompositeSegment_boundary_caesura {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val)
    (hz : z.val + 1 = (r.val i).val) (hi : i.val + 1 < Surjection.occurrenceCount u.val k) :
    Surjection.Caesura (positiveCompositeCutWord u v k r).val
      (positiveCompositeSegmentPosition u v k r i z) := by
  let j : Fin (Surjection.occurrenceCount u.val k) := ⟨i.val + 1, hi⟩
  have hp := positiveCompositeSegment_boundary_pair u v k r i j rfl
  have hs := IntervalCuts.substitute_prefix_length_at_occurrence u v k r i
  change compositePrefixLength u v k r ((Surjection.occurrenceAt u.val k i).val + 1) =
    compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val + (r.val i).val at hs
  have he : positiveCompositeSegmentPosition u v k r i z =
      compositeLastPosition u v k r (positiveOccurrencePosition u k i) := by
    apply Fin.ext
    change compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val + z.val =
      compositePrefixLength u v k r ((Surjection.occurrenceAt u.val k i).val + 1) - 1
    omega
  refine ⟨compositeFirstPosition u v k r (positiveOccurrencePosition u k j), ?_, ?_⟩
  · rw [he]
    exact hp.1
  · rw [he]
    exact hp.2.symm

end SerrePositivity.EInfinity.SimplexCuts
