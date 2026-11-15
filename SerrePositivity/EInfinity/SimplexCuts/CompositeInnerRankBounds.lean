module

public import SerrePositivity.EInfinity.SimplexCuts.ColorRankBoundComparisons
public import SerrePositivity.EInfinity.SimplexCuts.CompositeNestedMap
public import SerrePositivity.EInfinity.SimplexCuts.SegmentEdgeOwnerOrder

/-!
# 元の内側切断の順位の比較と同じ部分語の両端

Berger–Fresse §2.2.6、M14 L12a の左逆。
元の所属出現の順位区間を、同じ分割の開始・終了位置で特定する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C446：元の内側切断の高さは、同じ所属出現の順位区間内（BF §2.2.6）。 -/
lemma positiveCompositeInnerCut_rank_mem {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (a : Fin (n + e)) :
    cutHeights (positiveCompositeInnerCut u v k c) a ∈
      colorIntervalRanks (positiveCompositeOuterCut u v k c) (positiveWord u) k
        (positiveOccurrencePosition u k
          (segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val)) := by
  rw [positiveCompositeInnerCut_heights]
  exact colorHeightRank_mem _ _ _ _ _ _
    (positiveCompositeInnerEdge_height_bounds u v k c a).1
    (positiveCompositeInnerEdge_height_bounds u v k c a).2

/-- C447：元の内側順位と両端の比較は、同じ分割の開始・終了位置の比較（BF §2.2.6）。 -/
lemma positiveCompositeInnerCut_rank_bounds_iff {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (a : Fin (n + e)) (i : Fin (Surjection.occurrenceCount u.val k)) :
    (colorIntervalFirst (positiveCompositeOuterCut u v k c) (positiveWord u) k
        (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i) ≤
        cutHeights (positiveCompositeInnerCut u v k c) a ↔ c.1.start i ≤ a.val) ∧
    (cutHeights (positiveCompositeInnerCut u v k c) a ≤
        colorIntervalLast (positiveCompositeOuterCut u v k c) (positiveWord u) k
          (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i) ↔
      a.val + 1 < c.1.start i + (c.1.val i).val) := by
  have hmem := positiveCompositeInnerCut_rank_mem u v k c a
  constructor
  · rw [colorIntervalFirst_le_rank_iff _ _ _ _ _ (positiveOccurrencePosition_value u k _)
      (positiveOccurrencePosition_value u k i) _ hmem,
      (positiveOccurrencePosition_strictMono u k).le_iff_le,
      le_segmentEdgeOwner_iff]
  · rw [rank_le_colorIntervalLast_iff _ _ _ _ _ (positiveOccurrencePosition_value u k _)
      (positiveOccurrencePosition_value u k i) _ hmem,
      (positiveOccurrencePosition_strictMono u k).le_iff_le,
      segmentEdgeOwner_le_iff c.1 (Surjection.occurrenceCount_pos u k) a.val
        (by have h := a.isLt; omega)]

end SerrePositivity.EInfinity.SimplexCuts
