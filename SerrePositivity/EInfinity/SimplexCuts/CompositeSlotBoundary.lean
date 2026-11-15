module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentVertexRanks

/-!
# 隣接する元の挿入部分語の共有端点と外側の狭義の高さ

Berger–Fresse §2.2.6、M14 L12a のC453の外側指定色。
共有端点の二つの同色頂点を、元の非退化性で比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の隣接部分語の共有端点は異なる合成位置で同じラベル（BF §2.2.6）。 -/
lemma positiveCompositeSegment_boundary_pair {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i j : Fin (Surjection.occurrenceCount u.val k)) (hij : j.val = i.val + 1) :
    compositeLastPosition u v k r (positiveOccurrencePosition u k i) <
        compositeFirstPosition u v k r (positiveOccurrencePosition u k j) ∧
      (positiveCompositeCutWord u v k r).val
          (compositeLastPosition u v k r (positiveOccurrencePosition u k i)) =
        (positiveCompositeCutWord u v k r).val
          (compositeFirstPosition u v k r (positiveOccurrencePosition u k j)) := by
  let zi : Fin (r.val i).val := ⟨(r.val i).val - 1, by have h := r.positive (by omega) i; omega⟩
  let zj : Fin (r.val j).val := ⟨0, r.positive (by omega) j⟩
  have hs := IntervalCuts.substitute_prefix_length_at_occurrence u v k r i
  change compositePrefixLength u v k r ((Surjection.occurrenceAt u.val k i).val + 1) =
    compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val + (r.val i).val at hs
  have hp := r.positive (by omega : 0 < (n + 1) + e) i
  have heLast : positiveCompositeSegmentPosition u v k r i zi =
      compositeLastPosition u v k r (positiveOccurrencePosition u k i) := by
    apply Fin.ext
    change compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val +
      ((r.val i).val - 1) =
      compositePrefixLength u v k r ((Surjection.occurrenceAt u.val k i).val + 1) - 1
    omega
  have heFirst : positiveCompositeSegmentPosition u v k r j zj =
      compositeFirstPosition u v k r (positiveOccurrencePosition u k j) := by
    apply Fin.ext
    rfl
  constructor
  · rw [← heLast, ← heFirst]
    exact IntervalCuts.compositeSegmentPosition_lt u v k r i j
      (by change i.val < j.val; omega) zi zj
  · rw [← heLast, ← heFirst]
    simp only [positiveCompositeSegmentPosition_label]
    apply congrArg (BarrattEccles.insertedPosition m (n + 1) k)
    apply congrArg v.val
    apply Fin.ext
    change r.start i + ((r.val i).val - 1) = r.start j + 0
    exact (r.start_next i j hij).symm.trans (Nat.add_zero (r.start j)).symm

/-- 元の合成切断の非退化性は、外側の隣接する指定色の間の高さを厳密に離す（BF §2.2.6）。 -/
lemma positiveComposite_outer_slot_boundary_strict {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val)
    (i j : Fin (Surjection.occurrenceCount u.val k)) (hij : j.val = i.val + 1) :
    hi (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i) <
      lo (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k j) := by
  let a := compositeLastPosition u v k c.1 (positiveOccurrencePosition u k i)
  let b := compositeFirstPosition u v k c.1 (positiveOccurrencePosition u k j)
  let x := (intervalPositions c.2 a).max' (intervalPositions_nonempty c.2 a)
  let y := (intervalPositions c.2 b).min' (intervalPositions_nonempty c.2 b)
  have hx := horizontal_hi_vertex c.2 a
  have hy := horizontal_lo_vertex c.2 b
  have hp := positiveCompositeSegment_boundary_pair u v k c.1 i j hij
  have hxy : x < y := by
    by_contra hn
    have hm := c.2.horizontal.monotone (le_of_not_gt hn)
    rw [hx, hy] at hm
    exact (not_le_of_gt hp.1) hm
  have hlabels : label c.2 (positiveCompositeCutWord u v k c.1).val x =
      label c.2 (positiveCompositeCutWord u v k c.1).val y := by
    change (positiveCompositeCutWord u v k c.1).val (c.2.horizontal x) =
      (positiveCompositeCutWord u v k c.1).val (c.2.horizontal y)
    rw [hx, hy]
    exact hp.2
  have hv := vertex_strictMono_on_color h hxy hlabels
  rw [(positiveCompositeOuterCut_endpoints u v k c (positiveOccurrencePosition u k i)).2,
    (positiveCompositeOuterCut_endpoints u v k c (positiveOccurrencePosition u k j)).1]
  exact hv

end SerrePositivity.EInfinity.SimplexCuts
