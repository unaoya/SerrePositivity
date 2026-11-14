module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentRecovery
public import SerrePositivity.EInfinity.SimplexCuts.RecoveredPartitionValues
public import SerrePositivity.EInfinity.SimplexCuts.PositiveOccurrenceComparison
public import SerrePositivity.EInfinity.SimplexCuts.ColorRankPositionTransport

/-!
# 元の一段切断から同じ重なる分割への復元

Berger–Fresse §2.2.6、M14 L12a の左逆の証明分割。
元の出現番号と語長移送を保ち、同じ二端点から元の部分長へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C449：一段切断を二段へ射影して部分長を読むと、元の同じ分割に戻る（BF §2.2.6）。 -/
lemma positiveCompositeNestedMap_partition {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    positiveNestedPartition u v k (positiveCompositeNestedMap u v k c) = c.1 := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  let j : Fin (Surjection.occurrenceCount (positiveWord u).val k) :=
    Fin.cast (positiveWord_occurrenceCount u k).symm i
  rw [positiveNestedPartition_length u v k (positiveCompositeNestedMap u v k c) i j rfl]
  change hi (positiveCompositeInnerCut u v k c).exchange
      (colorOccurrenceLast (positiveCompositeOuterCut u v k c) (positiveWord u) k j) -
    lo (positiveCompositeInnerCut u v k c).exchange
      (colorOccurrenceFirst (positiveCompositeOuterCut u v k c) (positiveWord u) k j) + 1 =
    (c.1.val i).val
  unfold colorOccurrenceLast colorOccurrenceFirst
  rw [colorIntervalLast_congr_position _ _ _ _ _ _
      (positiveOccurrencePosition_value u k i) (positiveOccurrencePosition_eq u k i j rfl).symm,
    colorIntervalFirst_congr_position _ _ _ _ _ _
      (positiveOccurrencePosition_value u k i) (positiveOccurrencePosition_eq u k i j rfl).symm,
    positiveCompositeNestedMap_segmentStart, positiveCompositeNestedMap_segmentEnd]
  have hp := c.1.positive (by omega : 0 < (n + 1) + e) i
  omega

end SerrePositivity.EInfinity.SimplexCuts
