module

public import SerrePositivity.EInfinity.SimplexCuts.RecoveredPartitionStarts
public import SerrePositivity.EInfinity.SimplexCuts.CutHeightExchange
public import SerrePositivity.EInfinity.SimplexCuts.ColorRankIntervals

/-!
# 復元した同じ分割の内部の辺と元の順位

Berger–Fresse §2.2.6、M14 L12a の逆復元。
元の内側切断の交換経路の端点を、その同じ高さの順位の区間へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C423：復元分割の内部の辺の高さは、元の同じ順位区間内（BF §2.2.6）。 -/
lemma positiveNestedPartition_height_interval {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k))
    (j : Fin (Surjection.occurrenceCount (positiveWord u).val k)) (hij : i.val = j.val)
    (a : Fin (n + e)) (hl : (positiveNestedPartition u v k c).start i ≤ a.val)
    (hr : a.val + 1 < (positiveNestedPartition u v k c).start i +
      ((positiveNestedPartition u v k c).val i).val) :
    colorOccurrenceFirst c.1 (positiveWord u) k j ≤ cutHeights c.2 a ∧
      cutHeights c.2 a ≤ colorOccurrenceLast c.1 (positiveWord u) k j := by
  rw [positiveNestedPartition_start u v k c i j hij] at hl hr
  rw [positiveNestedPartition_length u v k c i j hij] at hr
  apply (cutHeights_mem_interval c.2 a _ _).mpr
  constructor
  · exact hl
  · change a.val < nestedSegmentEnd c.1 (positiveWord u) k c.2 j
    have hs := nestedSegmentStart_le_end c.1 (positiveWord u) k c.2 j
    omega

/-- C424：同じ順位区間の頂点は元の区間の高さの範囲内（BF §2.2.6）。 -/
lemma vertices_bounds_on_colorInterval {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1))
    (j : Fin (outputDegree s v a + 1)) (hj : j ∈ colorIntervalRanks s v a p) :
    lo s p ≤ (vertices s v a j).val ∧ (vertices s v a j).val ≤ hi s p := by
  let E := (colorPositions s v.val a).orderEmbOfFin (colorPositions_card_eq s v a)
  have h : s.horizontal (E j) = p := (Finset.mem_filter.mp hj).2
  exact ⟨lo_le_vertical s p (E j) h, vertical_le_hi s p (E j) h⟩

end SerrePositivity.EInfinity.SimplexCuts
