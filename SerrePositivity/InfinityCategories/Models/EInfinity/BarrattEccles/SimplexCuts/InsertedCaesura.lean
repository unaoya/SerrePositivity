module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.SegmentCaesuraFromInner
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositePositionDecomposition

/-!
模型。文献の定義との比較は後で
# 元の挿入色の区切りの全条件

Berger–Fresse §1.2.2・§2.2.4–6、M14 L12a のC452。
元の内側語の区切りと、次の部分語への共有端点の重複を分ける。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の挿入色の区切りは、内側の区切りか次の部分語との共有端点（BF §2.2.4）。 -/
lemma positiveComposite_inserted_caesura_iff {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k r i z) ↔
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentInnerWordPosition r i z) ∨
        (z.val + 1 = (r.val i).val ∧ i.val + 1 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) := by
  constructor
  · rintro ⟨a, ha, hval⟩
    have hlabel : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val a =
        _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m (n + 1) k (v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentInnerWordPosition r i z)) :=
      hval.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition_label u v k r i z)
    obtain ⟨j, w, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositePosition_of_inserted_label u v k r a
      (v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentInnerWordPosition r i z)) hlabel
    rw [he] at ha hval
    have hv : v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentInnerWordPosition r j w) = v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentInnerWordPosition r i z) := by
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.insertedPosition_injective m (n + 1) k
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition_label, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentInnerWordPosition] using hval
    rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegment_future_inner_order u v k r i j z w ha with hlt | ⟨_, hz, hi⟩
    · exact Or.inl ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentInnerWordPosition r j w, hlt, hv⟩
    · exact Or.inr ⟨hz, hi⟩
  · rintro (h | ⟨hz, hi⟩)
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegment_caesura_of_inner u v k r i z h
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegment_boundary_caesura u v k r i z hz hi

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
