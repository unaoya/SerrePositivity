module

public import SerrePositivity.EInfinity.SimplexCuts.ConsecutiveCaesuraCounts
public import SerrePositivity.EInfinity.SimplexCuts.PositiveOccurrenceCaesuras
public import SerrePositivity.EInfinity.SimplexCuts.InsertedCaesuraBoundaryWeights

/-!
# 元の挿入部分語の区切り総数

Berger–Fresse §1.2.5・§2.2.4・§2.2.6、M14 L12a の C452。
内部の区切り数は同じ成分次数、末尾は元の外側の区切りを一つだけ数える。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ挿入部分語の区切り総数は、元の成分次数と外側区切りの和（BF §2.2.6）。 -/
lemma positiveComposite_segment_caesura_sum {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    (∑ z : Fin (r.val i).val, if Surjection.Caesura (positiveCompositeCutWord u v k r).val
        (positiveCompositeSegmentPosition u v k r i z) then 1 else 0 : ℕ) =
      Surjection.segmentDegree v.val r i +
        if Surjection.Caesura (positiveWord u).val (positiveOccurrencePosition u k i)
        then 1 else 0 := by
  have hlen : 0 < (r.val i).val := r.positive (by omega) i
  have hbefore :
      (∑ z : Fin ((r.val i).val - 1),
        if Surjection.Caesura (positiveCompositeCutWord u v k r).val
          (positiveCompositeSegmentPosition u v k r i ⟨z.val, by have hz := z.isLt; omega⟩)
        then 1 else 0 : ℕ) = Surjection.segmentDegree v.val r i := by
    calc
      _ = ∑ z : Fin ((r.val i).val - 1), if Surjection.Caesura v.val
          ⟨r.start i + z.val, by have hb := r.start_add_length_le i; have hz := z.isLt; omega⟩
          then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        rw [positiveComposite_inserted_caesura_indicator,
          ite_eq_right (by have hz := z.isLt; omega : z.val + 1 ≠ (r.val i).val)]
        rfl
      _ = _ := by
        have hc := sum_consecutive_caesuraIndicators v.val (r.start i) ((r.val i).val - 1)
          (by have hb := r.start_add_length_le i; omega)
        have he : r.start i + ((r.val i).val - 1) = r.start i + (r.val i).val - 1 := by omega
        have hr := congrArg (Surjection.lineRank v.val) he
        unfold Surjection.segmentDegree
        omega
  have hend : (if Surjection.Caesura (positiveCompositeCutWord u v k r).val
      (positiveCompositeSegmentPosition u v k r i ⟨(r.val i).val - 1, by omega⟩)
      then 1 else 0 : ℕ) =
      if Surjection.Caesura (positiveWord u).val (positiveOccurrencePosition u k i)
      then 1 else 0 := by
    rw [positiveComposite_inserted_caesura_indicator,
      ite_eq_left (by omega : (r.val i).val - 1 + 1 = (r.val i).val)]
    simp only [positiveOccurrencePosition_caesura_iff]
  rw [sum_fin_last hlen (fun z => if Surjection.Caesura (positiveCompositeCutWord u v k r).val
    (positiveCompositeSegmentPosition u v k r i z) then 1 else 0), hbefore, hend]

end SerrePositivity.EInfinity.SimplexCuts
