module

public import SerrePositivity.EInfinity.SimplexCuts.RemainingCaesuraWeights
public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentIntervalWidths
public import SerrePositivity.EInfinity.SimplexCuts.PositiveOccurrenceCaesuras
public import SerrePositivity.EInfinity.SimplexCuts.ConsecutiveCaesuraCounts
public import SerrePositivity.EInfinity.SimplexCuts.InsertedCaesuraBoundaryWeights

/-!
# 元の位置指数の残り位置・部分語末尾・内部の項

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
同じ元の区切りの高さを、既存のブロック両端を保って分ける。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の残り位置の位置指数の項は、外側の同じ項（BF §2.2.6）。 -/
lemma positiveComposite_remaining_positionTerm {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k) :
    (if Surjection.Caesura (positiveCompositeCutWord u v k c.1).val
        (compositeFirstPosition u v k c.1 p) then
      hi c.2 (compositeFirstPosition u v k c.1 p) else 0) =
    (if Surjection.Caesura (positiveWord u).val p then
      hi (positiveCompositeOuterCut u v k c) p else 0) := by
  have hh : hi c.2 (compositeFirstPosition u v k c.1 p) =
      hi (positiveCompositeOuterCut u v k c) p :=
    (congrArg (hi c.2) (compositeFirstPosition_eq_last_of_non_slot u v k c.1 p hp)).trans
      (positiveCompositeOuterCut_endpoints u v k c p).2.symm
  simp only [positiveComposite_remaining_caesura_iff u v k c.1 p hp, hh]

/-- 同じ部分語の末尾は外側の区切りへ、内部は同じ内部区切りへ戻す（BF §2.2.6）。 -/
lemma positiveComposite_segment_positionTerm_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    (∑ z : Fin (c.1.val i).val,
      if Surjection.Caesura (positiveCompositeCutWord u v k c.1).val
          (positiveCompositeSegmentPosition u v k c.1 i z) then
        hi c.2 (positiveCompositeSegmentPosition u v k c.1 i z) else 0) =
    (if Surjection.Caesura (positiveWord u).val (positiveOccurrencePosition u k i) then
      hi (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i) else 0) +
    ∑ z : Fin ((c.1.val i).val - 1),
      if Surjection.Caesura v.val
          ⟨c.1.start i + z.val, by have hb := c.1.start_add_length_le i; have hz := z.isLt; omega⟩
      then hi c.2 (positiveCompositeSegmentPosition u v k c.1 i
        ⟨z.val, by have hz := z.isLt; omega⟩) else 0 := by
  have hlen : 0 < (c.1.val i).val := c.1.positive (by omega) i
  let Z : Fin (c.1.val i).val := ⟨(c.1.val i).val - 1, by omega⟩
  have hend : (if Surjection.Caesura (positiveCompositeCutWord u v k c.1).val
      (positiveCompositeSegmentPosition u v k c.1 i Z) then
      hi c.2 (positiveCompositeSegmentPosition u v k c.1 i Z) else 0) =
      if Surjection.Caesura (positiveWord u).val (positiveOccurrencePosition u k i) then
        hi (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i) else 0 := by
    have he := (positiveComposite_inserted_end_caesura_iff u v k c.1 i Z
      (by dsimp only [Z]; omega)).trans (positiveOccurrencePosition_caesura_iff u k i).symm
    simp only [he]
    rw [(positiveCompositeSegmentPosition_endpoints u v k c.1 i).2,
      ← (positiveCompositeOuterCut_endpoints u v k c (positiveOccurrencePosition u k i)).2]
  have hbefore :
      (∑ z : Fin ((c.1.val i).val - 1),
        if Surjection.Caesura (positiveCompositeCutWord u v k c.1).val
          (positiveCompositeSegmentPosition u v k c.1 i
            ⟨z.val, by have hz := z.isLt; omega⟩) then
          hi c.2 (positiveCompositeSegmentPosition u v k c.1 i
            ⟨z.val, by have hz := z.isLt; omega⟩) else 0) =
      ∑ z : Fin ((c.1.val i).val - 1), if Surjection.Caesura v.val
          ⟨c.1.start i + z.val, by have hb := c.1.start_add_length_le i; have hz := z.isLt; omega⟩
        then hi c.2 (positiveCompositeSegmentPosition u v k c.1 i
          ⟨z.val, by have hz := z.isLt; omega⟩) else 0 := by
    apply Finset.sum_congr rfl
    intro z _
    simp only [positiveComposite_inserted_caesura_split_iff,
      ite_eq_right (by have hz := z.isLt; omega : z.val + 1 ≠ (c.1.val i).val),
      segmentInnerWordPosition]
  rw [sum_fin_last hlen (fun z => if Surjection.Caesura (positiveCompositeCutWord u v k c.1).val
    (positiveCompositeSegmentPosition u v k c.1 i z) then
      hi c.2 (positiveCompositeSegmentPosition u v k c.1 i z) else 0), hbefore, hend]
  exact Nat.add_comm _ _

end SerrePositivity.EInfinity.SimplexCuts
