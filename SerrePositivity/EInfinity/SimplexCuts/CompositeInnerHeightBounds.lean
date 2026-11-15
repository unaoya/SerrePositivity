module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeHeightBounds
public import SerrePositivity.EInfinity.SimplexCuts.CompositeInnerEdges
public import SerrePositivity.EInfinity.SimplexCuts.PositiveOccurrencePosition

/-!
# 元の内側水平辺の高さと同じ外側区間

Berger–Fresse §2.2.6、M14 L12a。
所属部分語の元の接頭長を、同じ外側区間の高さの範囲へ接続する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C413：元の内側辺の高さは、所属する同じ外側区間の範囲内（BF §2.2.6）。 -/
lemma positiveCompositeInnerEdge_height_bounds {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (a : Fin (n + e)) :
    lo (positiveCompositeOuterCut u v k c)
        (positiveOccurrencePosition u k
          (segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val)) ≤
        (cutHeights c.2 (compositeInnerEdge u v k c.1 a)).val ∧
      (cutHeights c.2 (compositeInnerEdge u v k c.1 a)).val ≤
        hi (positiveCompositeOuterCut u v k c)
          (positiveOccurrencePosition u k
            (segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val)) := by
  let j := segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val
  apply positiveCompositeOuterCut_height_bounds
  · change compositePrefixLength u v k c.1 (Surjection.occurrenceAt u.val k j).val ≤ _
    rw [compositeInnerEdge_val]
    exact Nat.le_add_right _ _
  · change (compositeInnerEdge u v k c.1 a).val + 1 <
      compositePrefixLength u v k c.1 ((Surjection.occurrenceAt u.val k j).val + 1)
    change _ < (Surjection.substitute k
      ((List.ofFn u.val).take ((Surjection.occurrenceAt u.val k j).val + 1))
      (c.1.segments v.val)).length
    rw [IntervalCuts.substitute_prefix_length_at_occurrence, compositeInnerEdge_val]
    have hl := segmentEdgeOwner_start_le c.1 (Surjection.occurrenceCount_pos u k) a.val
    have hr := segmentEdgeOwner_end_gt c.1 (Surjection.occurrenceCount_pos u k) a.val
      (by have h := a.isLt; omega)
    change c.1.start j ≤ a.val at hl
    change a.val + 1 < c.1.start j + (c.1.val j).val at hr
    change compositePrefixLength u v k c.1 (Surjection.occurrenceAt u.val k j).val +
        (a.val - c.1.start j) + 1 <
      compositePrefixLength u v k c.1 (Surjection.occurrenceAt u.val k j).val +
        (c.1.val j).val
    omega

end SerrePositivity.EInfinity.SimplexCuts
