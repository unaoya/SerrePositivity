module

public import SerrePositivity.EInfinity.SimplexCuts.NestedPartitionHeightInterval
public import SerrePositivity.EInfinity.SimplexCuts.PositiveOccurrenceComparison
public import SerrePositivity.EInfinity.SimplexCuts.SegmentEdgeOwner

/-!
# 元の二段切断から読む内側高さの範囲

Berger–Fresse §2.2.6、M14 L12a の逆復元。
復元した同じ分割の所属から、元の色別頂点写像の高さの上下界を読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C430：元の先の区間の終点は、後の区間の始点以下（BF §2.2.3）。 -/
lemma hi_le_lo_of_lt {m q : ℕ} (s : Cut m q) (i j : Fin (m + 1)) (hij : i < j) :
    hi s i ≤ lo s j := by
  let a : Fin m := ⟨i.val, by have h := j.isLt; have hv : i.val < j.val := hij; omega⟩
  have he : i = a.castSucc := Fin.ext rfl
  rw [he, hi_eq_lo_succ]
  apply lo_monotone
  change i.val + 1 ≤ j.val
  exact hij

/-- C431：同じ二段切断の内側高さは、元の所属出現の外側区間内（BF §2.2.6）。 -/
lemma positiveNestedInnerHeight_bounds {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) (a : Fin (n + e)) :
    lo c.1 (positiveOccurrencePosition u k
        (segmentEdgeOwner (positiveNestedPartition u v k c)
          (Surjection.occurrenceCount_pos u k) a.val)) ≤
        (vertices c.1 (positiveWord u) k (cutHeights c.2 a)).val ∧
      (vertices c.1 (positiveWord u) k (cutHeights c.2 a)).val ≤
        hi c.1 (positiveOccurrencePosition u k
          (segmentEdgeOwner (positiveNestedPartition u v k c)
            (Surjection.occurrenceCount_pos u k) a.val)) := by
  let i := segmentEdgeOwner (positiveNestedPartition u v k c)
    (Surjection.occurrenceCount_pos u k) a.val
  let j : Fin (Surjection.occurrenceCount (positiveWord u).val k) :=
    Fin.cast (positiveWord_occurrenceCount u k).symm i
  have hl := segmentEdgeOwner_start_le (positiveNestedPartition u v k c)
    (Surjection.occurrenceCount_pos u k) a.val
  have hr := segmentEdgeOwner_end_gt (positiveNestedPartition u v k c)
    (Surjection.occurrenceCount_pos u k) a.val (by have h := a.isLt; omega)
  have hinterval := positiveNestedPartition_height_interval u v k c i j rfl a hl hr
  have hmem : cutHeights c.2 a ∈ colorIntervalRanks c.1 (positiveWord u) k
      (Surjection.occurrenceAt (positiveWord u).val k j) := by
    rw [colorIntervalRanks_eq_Icc c.1 (positiveWord u) k _
      (Surjection.occurrenceAt_value (positiveWord u).val k j)]
    exact Finset.mem_Icc.mpr hinterval
  have h := vertices_bounds_on_colorInterval c.1 (positiveWord u) k _ _ hmem
  rw [← positiveOccurrencePosition_eq u k i j rfl] at h
  exact h

end SerrePositivity.EInfinity.SimplexCuts
