module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.SegmentPositionOrder
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.SegmentBoundaryCaesura

/-!
模型。文献の定義との比較は後で
# 元の内側語の後の同色位置を合成語の後の位置で読む

Berger–Fresse §1.2.2・§2.2.4、M14 L12a のC452。
元の内側の後の位置の直前の辺を含む部分語を用い、同じ後のラベルを代入する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の内側語の区切りは、同じ部分語内位置で合成語の区切りとなる（BF §2.2.4）。 -/
lemma positiveCompositeSegment_caesura_of_inner {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentInnerWordPosition r i z)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k r i z) := by
  obtain ⟨a, ha, hval⟩ := h
  have haVal : r.start i + z.val < a.val := ha
  let b : Fin (n + e) := ⟨a.val - 1, by have hb := a.isLt; omega⟩
  have hba : b.val + 1 = a.val := by dsimp only [b]; omega
  let j := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) b.val
  have hs : r.start j ≤ b.val :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner_start_le r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) b.val
  have ht : b.val + 1 < r.start j + (r.val j).val :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner_end_gt r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) b.val
      (by have hb := b.isLt; omega)
  let w : Fin (r.val j).val := ⟨a.val - r.start j, by omega⟩
  have hw : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentInnerWordPosition r j w = a := by
    apply Fin.ext
    change r.start j + (a.val - r.start j) = a.val
    omega
  have hij : i ≤ j := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.le_segmentEdgeOwner_iff r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) b.val i).mpr
    (by omega)
  have hpos : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k r i z <
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k r j w := by
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition_lt_iff u v k r i j z w).mpr
    rcases eq_or_lt_of_le hij with he | hlt
    · apply Or.inr
      refine ⟨he, ?_⟩
      have heStart := congrArg r.start he
      have hwVal : w.val = a.val - r.start j := rfl
      omega
    · exact Or.inl hlt
  refine ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k r j w, hpos, ?_⟩
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition_label]
  apply congrArg (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m (n + 1) k)
  exact (congrArg v.val hw).trans hval

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
