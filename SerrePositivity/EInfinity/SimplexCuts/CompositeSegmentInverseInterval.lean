module

public import SerrePositivity.EInfinity.SimplexCuts.InnerVertexSegmentCoverage
public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentInnerVertices
public import SerrePositivity.EInfinity.SimplexCuts.ColorHeightRankInverse

/-!
# 元の内側順位から合成切断の同じ区間へ戻す

Berger–Fresse §2.2.6、M14 L12a のC451の逆方向。
部分語の両端では外側区間を、内部では同じ内側辺の高さを読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ内側区間の順位は、元の合成語の同じ区間の高さとなる（BF §2.2.6）。 -/
lemma positiveCompositeSegment_inverse_interval {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (rank : Fin (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1))
    (hm : rank ∈ colorIntervalRanks (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i))
    (hl : lo (positiveCompositeInnerCut u v k c)
      (positiveCompositeSegmentInnerPosition u v k c i z) ≤ rank.val)
    (hr : rank.val ≤ hi (positiveCompositeInnerCut u v k c)
      (positiveCompositeSegmentInnerPosition u v k c i z)) :
    lo c.2 (positiveCompositeSegmentPosition u v k c.1 i z) ≤
        (vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k rank).val ∧
      (vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k rank).val ≤
        hi c.2 (positiveCompositeSegmentPosition u v k c.1 i z) := by
  let j := positiveCompositeSegmentInnerPosition u v k c i z
  have hj : j.val = c.1.start i + z.val := rfl
  have hz := z.isLt
  have hb := c.1.start_add_length_le i
  have houter := positiveCompositeOuterCut_endpoints u v k c (positiveOccurrencePosition u k i)
  have hvertex := vertices_bounds_on_colorInterval (positiveCompositeOuterCut u v k c)
    (positiveWord u) k (positiveOccurrencePosition u k i) rank hm
  constructor
  · by_cases hz0 : z.val = 0
    · have hePos : positiveCompositeSegmentPosition u v k c.1 i z =
          compositeFirstPosition u v k c.1 (positiveOccurrencePosition u k i) := by
        apply Fin.ext
        change compositePrefixLength u v k c.1 (Surjection.occurrenceAt u.val k i).val + z.val =
          compositePrefixLength u v k c.1 (Surjection.occurrenceAt u.val k i).val
        omega
      rw [hePos, ← houter.1]
      exact hvertex.1
    · let a : Fin (n + e) := ⟨j.val - 1, by have ha := j.isLt; omega⟩
      have hja : j = a.succ := Fin.ext (by dsimp only [a]; simp only [Fin.val_succ]; omega)
      have ha : a.val + 1 = j.val := by dsimp only [a]; omega
      have heOwner : segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val = i := by
        apply segmentEdgeOwner_unique
        · have h := a.isLt; omega
        · omega
        · omega
      have hePos : (compositeInnerEdge u v k c.1 a).succ =
          positiveCompositeSegmentPosition u v k c.1 i z := by
        apply Fin.ext
        simp only [Fin.val_succ, compositeInnerEdge_val, heOwner,
          positiveCompositeSegmentPosition_val]
        omega
      have hc : cutHeights (positiveCompositeInnerCut u v k c) a ≤ rank := by
        change lo (positiveCompositeInnerCut u v k c) j ≤ rank.val at hl
        rw [hja, ← hi_eq_lo_succ] at hl
        exact hl
      have hv := (vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k).monotone hc
      rw [positiveCompositeInnerCut_vertices] at hv
      rw [← hePos, ← hi_eq_lo_succ]
      exact hv
  · by_cases hzlast : z.val + 1 = (c.1.val i).val
    · have hs := IntervalCuts.substitute_prefix_length_at_occurrence u v k c.1 i
      change compositePrefixLength u v k c.1 ((Surjection.occurrenceAt u.val k i).val + 1) =
        compositePrefixLength u v k c.1 (Surjection.occurrenceAt u.val k i).val +
          (c.1.val i).val at hs
      have hePos : positiveCompositeSegmentPosition u v k c.1 i z =
          compositeLastPosition u v k c.1 (positiveOccurrencePosition u k i) := by
        apply Fin.ext
        change compositePrefixLength u v k c.1 (Surjection.occurrenceAt u.val k i).val + z.val =
          compositePrefixLength u v k c.1 ((Surjection.occurrenceAt u.val k i).val + 1) - 1
        omega
      rw [hePos, ← houter.2]
      exact hvertex.2
    · let a : Fin (n + e) := ⟨j.val, by have ha := j.isLt; omega⟩
      have hja : j = a.castSucc := Fin.ext rfl
      have ha : a.val = j.val := rfl
      have heOwner : segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val = i := by
        apply segmentEdgeOwner_unique
        · have h := a.isLt; omega
        · omega
        · omega
      have hePos : (compositeInnerEdge u v k c.1 a).castSucc =
          positiveCompositeSegmentPosition u v k c.1 i z := by
        apply Fin.ext
        simp only [Fin.val_castSucc, compositeInnerEdge_val, heOwner,
          positiveCompositeSegmentPosition_val]
        omega
      have hc : rank ≤ cutHeights (positiveCompositeInnerCut u v k c) a := by
        change rank.val ≤ hi (positiveCompositeInnerCut u v k c) j at hr
        rw [hja] at hr
        exact hr
      have hv := (vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k).monotone hc
      rw [positiveCompositeInnerCut_vertices] at hv
      rw [← hePos]
      exact hv

end SerrePositivity.EInfinity.SimplexCuts
