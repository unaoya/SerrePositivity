module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ColorRankBoundComparisons
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeNestedMap
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.SegmentEdgeOwnerOrder

/-!
模型。文献の定義との比較は後で
# 元の内側切断の順位の比較と同じ部分語の両端

Berger–Fresse §2.2.6、M14 L12a の左逆。
元の所属出現の順位区間を、同じ分割の開始・終了位置で特定する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C446：元の内側切断の高さは、同じ所属出現の順位区間内（BF §2.2.6）。 -/
lemma positiveCompositeInnerCut_rank_mem {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q) (a : Fin (n + e)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c) a ∈
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalRanks (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) a.val)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut_heights]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorHeightRank_mem _ _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerEdge_height_bounds u v k c a).1
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerEdge_height_bounds u v k c a).2

/-- C447：元の内側順位と両端の比較は、同じ分割の開始・終了位置の比較（BF §2.2.6）。 -/
lemma positiveCompositeInnerCut_rank_bounds_iff {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q)
    (a : Fin (n + e)) (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalFirst (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_value u k i) ≤
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c) a ↔ c.1.start i ≤ a.val) ∧
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c) a ≤
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalLast (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_value u k i) ↔
      a.val + 1 < c.1.start i + (c.1.val i).val) := by
  have hmem := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut_rank_mem u v k c a
  constructor
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalFirst_le_rank_iff _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_value u k _)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_value u k i) _ hmem,
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_strictMono u k).le_iff_le,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.le_segmentEdgeOwner_iff]
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rank_le_colorIntervalLast_iff _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_value u k _)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_value u k i) _ hmem,
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_strictMono u k).le_iff_le,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner_le_iff c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) a.val
        (by have h := a.isLt; omega)]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
