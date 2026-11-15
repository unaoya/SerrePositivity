module

public import SerrePositivity.EInfinity.SimplexCuts.SegmentCaesuraFromInner
public import SerrePositivity.EInfinity.SimplexCuts.CompositePositionDecomposition

/-!
# 元の挿入色の区切りの全条件

Berger–Fresse §1.2.2・§2.2.4–6、M14 L12a のC452。
元の内側語の区切りと、次の部分語への共有端点の重複を分ける。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の挿入色の区切りは、内側の区切りか次の部分語との共有端点（BF §2.2.4）。 -/
lemma positiveComposite_inserted_caesura_iff {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    Surjection.Caesura (positiveCompositeCutWord u v k r).val
        (positiveCompositeSegmentPosition u v k r i z) ↔
      Surjection.Caesura v.val (segmentInnerWordPosition r i z) ∨
        (z.val + 1 = (r.val i).val ∧ i.val + 1 < Surjection.occurrenceCount u.val k) := by
  constructor
  · rintro ⟨a, ha, hval⟩
    have hlabel : (positiveCompositeCutWord u v k r).val a =
        BarrattEccles.insertedPosition m (n + 1) k (v.val (segmentInnerWordPosition r i z)) :=
      hval.trans (positiveCompositeSegmentPosition_label u v k r i z)
    obtain ⟨j, w, he⟩ := positiveCompositePosition_of_inserted_label u v k r a
      (v.val (segmentInnerWordPosition r i z)) hlabel
    rw [he] at ha hval
    have hv : v.val (segmentInnerWordPosition r j w) = v.val (segmentInnerWordPosition r i z) := by
      apply Surjection.insertedPosition_injective m (n + 1) k
      simpa only [positiveCompositeSegmentPosition_label, segmentInnerWordPosition] using hval
    rcases positiveCompositeSegment_future_inner_order u v k r i j z w ha with hlt | ⟨_, hz, hi⟩
    · exact Or.inl ⟨segmentInnerWordPosition r j w, hlt, hv⟩
    · exact Or.inr ⟨hz, hi⟩
  · rintro (h | ⟨hz, hi⟩)
    · exact positiveCompositeSegment_caesura_of_inner u v k r i z h
    · exact positiveCompositeSegment_boundary_caesura u v k r i z hz hi

end SerrePositivity.EInfinity.SimplexCuts
