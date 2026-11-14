module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeInnerHeightBounds
public import SerrePositivity.EInfinity.SimplexCuts.ColorHeightVertices

/-!
# 同じ合成切断から読む元の内側切断の高さ

Berger–Fresse §2.2.6、M14 L12a の順方向。
同じ所属部分語の高さを、その外側区間の元の色別順位で読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C414：元の内側辺の高さを同じ色別順位で読む単調写像（BF §2.2.6）。 -/
def positiveCompositeInnerHeights {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    Fin (n + e) →o
      Fin (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1) where
  toFun a := colorHeightRank (positiveCompositeOuterCut u v k c) (positiveWord u) k
    (positiveOccurrencePosition u k
      (segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val))
    (positiveOccurrencePosition_value u k _)
    (cutHeights c.2 (compositeInnerEdge u v k c.1 a)).val
    (positiveCompositeInnerEdge_height_bounds u v k c a).1
    (positiveCompositeInnerEdge_height_bounds u v k c a).2
  monotone' := by
    intro a b hab
    let i := segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val
    let j := segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) b.val
    have hij : i ≤ j := segmentEdgeOwner_monotone c.1
      (Surjection.occurrenceCount_pos u k) (show a.val ≤ b.val from hab)
    change colorHeightRank (positiveCompositeOuterCut u v k c) (positiveWord u) k
        (positiveOccurrencePosition u k i) _ _ _ _ ≤
      colorHeightRank (positiveCompositeOuterCut u v k c) (positiveWord u) k
        (positiveOccurrencePosition u k j) _ _ _ _
    rcases eq_or_lt_of_le hij with he | hlt
    · simp only [he]
      apply colorHeightRank_monotone
      exact (cutHeights c.2).monotone ((compositeInnerEdge_strictMono u v k c.1).monotone hab)
    · apply le_of_lt
      apply colorIntervalRanks_ordered (positiveCompositeOuterCut u v k c) (positiveWord u) k
        (positiveOccurrencePosition u k i) (positiveOccurrencePosition u k j)
        (positiveOccurrencePosition_strictMono u k hlt)
      · exact colorHeightRank_mem _ _ _ _ _ _ _ _
      · exact colorHeightRank_mem _ _ _ _ _ _ _ _

end SerrePositivity.EInfinity.SimplexCuts
