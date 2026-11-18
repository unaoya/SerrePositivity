module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeSegmentRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.RecoveredPartitionValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveOccurrenceComparison
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ColorRankPositionTransport

/-!
模型。文献の定義との比較は後で
# 元の一段切断から同じ重なる分割への復元

Berger–Fresse §2.2.6、M14 L12a の左逆の証明分割。
元の出現番号と語長移送を保ち、同じ二端点から元の部分長へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C449：一段切断を二段へ射影して部分長を読むと、元の同じ分割に戻る（BF §2.2.6）。 -/
lemma positiveCompositeNestedMap_partition {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveNestedPartition u v k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedMap u v k c) = c.1 := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  let j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val k) :=
    Fin.cast (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord_occurrenceCount u k).symm i
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveNestedPartition_length u v k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedMap u v k c) i j rfl]
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c).exchange
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorOccurrenceLast (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k j) -
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c).exchange
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorOccurrenceFirst (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k j) + 1 =
    (c.1.val i).val
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorOccurrenceLast _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorOccurrenceFirst
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalLast_congr_position _ _ _ _ _ _
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_value u k i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_eq u k i j rfl).symm,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalFirst_congr_position _ _ _ _ _ _
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_value u k i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_eq u k i j rfl).symm,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedMap_segmentStart, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeNestedMap_segmentEnd]
  have hp := c.1.positive (by omega : 0 < (n + 1) + e) i
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
