module

public import SerrePositivity.EInfinity.SimplexCuts.ColorHeightRankInverse
public import SerrePositivity.EInfinity.SimplexCuts.NestedInnerHeightBounds

/-!
# 元の二段切断の同じ内側順位の復元

Berger–Fresse §2.2.6、M14 L12a の逆の等式の証明分割。
元の所属出現の区間内で、指定頂点の高さから同じ順位へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C437：元の内側高さの順位は、同じ所属出現の色別区間内（BF §2.2.6）。 -/
lemma positiveNestedInnerRank_mem {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) (a : Fin (n + e)) :
    cutHeights c.2 a ∈ colorIntervalRanks c.1 (positiveWord u) k
      (positiveOccurrencePosition u k
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
  rw [positiveOccurrencePosition_eq u k i j rfl,
    colorIntervalRanks_eq_Icc c.1 (positiveWord u) k _
      (Surjection.occurrenceAt_value (positiveWord u).val k j)]
  exact Finset.mem_Icc.mpr (positiveNestedPartition_height_interval u v k c i j rfl a hl hr)

/-- C438：指定した元の頂点の高さから、同じ内側順位に戻る（BF §2.2.6）。 -/
lemma positiveNestedInnerRank_recover {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) (a : Fin (n + e)) :
    colorHeightRank c.1 (positiveWord u) k
        (positiveOccurrencePosition u k
          (segmentEdgeOwner (positiveNestedPartition u v k c)
            (Surjection.occurrenceCount_pos u k) a.val))
        (positiveOccurrencePosition_value u k _)
        (vertices c.1 (positiveWord u) k (cutHeights c.2 a)).val
        (positiveNestedInnerHeight_bounds u v k c a).1
        (positiveNestedInnerHeight_bounds u v k c a).2 = cutHeights c.2 a :=
  colorHeightRank_vertices _ _ _ _ _ _ (positiveNestedInnerRank_mem u v k c a)

end SerrePositivity.EInfinity.SimplexCuts
