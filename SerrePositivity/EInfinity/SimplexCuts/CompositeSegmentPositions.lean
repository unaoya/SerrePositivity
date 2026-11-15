module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeInnerEdges
public import SerrePositivity.EInfinity.SimplexCuts.PositiveOccurrencePosition
public import SerrePositivity.EInfinity.SimplexCuts.FaceDataCompositionTransport

/-!
# 元の挿入部分語の位置を同じ切断語で読む

Berger–Fresse §1.2.4・§2.2.6、M14 L12a のC451の挿入色の照合。
既存のcompositeSegmentPositionの語長だけを切断の添字へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ部分語の元の位置を切断語長で読む（BF §2.2.6）。 -/
def positiveCompositeSegmentPosition {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    Fin (m + n + (d + e) + 1) :=
  ⟨(IntervalCuts.compositeSegmentPosition u v k r i z).val, by
    have h := (IntervalCuts.compositeSegmentPosition u v k r i z).isLt
    omega⟩

/-- 同じ部分語の位置は元の接頭長と相対位置の和（BF §2.2.6）。 -/
lemma positiveCompositeSegmentPosition_val {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    (positiveCompositeSegmentPosition u v k r i z).val =
      compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val + z.val := rfl

/-- 元の部分語の同じ位置には、同じ挿入ラベルがある（BF §2.2.6）。 -/
lemma positiveCompositeSegmentPosition_label {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    (positiveCompositeCutWord u v k r).val (positiveCompositeSegmentPosition u v k r i z) =
      BarrattEccles.insertedPosition m (n + 1) k
        (v.val ⟨r.start i + z.val, by
          have h := r.start_add_length_le i; have hz := z.isLt; omega⟩) := by
  calc
    _ = (Surjection.compositeBasisWord u v k r (by omega)).val
        (IntervalCuts.compositeSegmentPosition u v k r i z) := by
      unfold positiveCompositeCutWord
      exact word_eq_mp_value (by omega) _ _ _ rfl
    _ = _ := IntervalCuts.compositeSegmentPosition_value u v k r (by omega) i z

end SerrePositivity.EInfinity.SimplexCuts
