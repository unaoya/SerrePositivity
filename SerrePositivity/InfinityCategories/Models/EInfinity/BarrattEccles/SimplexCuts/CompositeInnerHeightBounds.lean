module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeHeightBounds
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeInnerEdges
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveOccurrencePosition

/-!
模型。文献の定義との比較は後で
# 元の内側水平辺の高さと同じ外側区間

Berger–Fresse §2.2.6、M14 L12a。
所属部分語の元の接頭長を、同じ外側区間の高さの範囲へ接続する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C413：元の内側辺の高さは、所属する同じ外側区間の範囲内（BF §2.2.6）。 -/
lemma positiveCompositeInnerEdge_height_bounds {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q) (a : Fin (n + e)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) a.val)) ≤
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights c.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeInnerEdge u v k c.1 a)).val ∧
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights c.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeInnerEdge u v k c.1 a)).val ≤
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) a.val)) := by
  let j := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) a.val
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut_height_bounds
  · change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k j).val ≤ _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeInnerEdge_val]
    exact Nat.le_add_right _ _
  · change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeInnerEdge u v k c.1 a).val + 1 <
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k j).val + 1)
    change _ < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k
      ((List.ofFn u.val).take ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k j).val + 1))
      (c.1.segments v.val)).length
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_at_occurrence, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeInnerEdge_val]
    have hl := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner_start_le c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) a.val
    have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner_end_gt c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) a.val
      (by have h := a.isLt; omega)
    change c.1.start j ≤ a.val at hl
    change a.val + 1 < c.1.start j + (c.1.val j).val at hr
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k j).val +
        (a.val - c.1.start j) + 1 <
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k j).val +
        (c.1.val j).val
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
