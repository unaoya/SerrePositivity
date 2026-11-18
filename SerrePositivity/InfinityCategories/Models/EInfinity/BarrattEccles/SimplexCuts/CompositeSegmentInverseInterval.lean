module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.InnerVertexSegmentCoverage
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeSegmentInnerVertices
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ColorHeightRankInverse

/-!
模型。文献の定義との比較は後で
# 元の内側順位から合成切断の同じ区間へ戻す

Berger–Fresse §2.2.6、M14 L12a のC451の逆方向。
部分語の両端では外側区間を、内部では同じ内側辺の高さを読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 同じ内側区間の順位は、元の合成語の同じ区間の高さとなる（BF §2.2.6）。 -/
lemma positiveCompositeSegment_inverse_interval {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (rank : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k + 1))
    (hm : rank ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorIntervalRanks (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i))
    (hl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentInnerPosition u v k c i z) ≤ rank.val)
    (hr : rank.val ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentInnerPosition u v k c i z)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo c.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k c.1 i z) ≤
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k rank).val ∧
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k rank).val ≤
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi c.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k c.1 i z) := by
  let j := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentInnerPosition u v k c i z
  have hj : j.val = c.1.start i + z.val := rfl
  have hz := z.isLt
  have hb := c.1.start_add_length_le i
  have houter := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut_endpoints u v k c (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i)
  have hvertex := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices_bounds_on_colorInterval (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i) rank hm
  constructor
  · by_cases hz0 : z.val = 0
    · have hePos : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k c.1 i z =
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeFirstPosition u v k c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i) := by
        apply Fin.ext
        change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val + z.val =
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val
        omega
      rw [hePos, ← houter.1]
      exact hvertex.1
    · let a : Fin (n + e) := ⟨j.val - 1, by have ha := j.isLt; omega⟩
      have hja : j = a.succ := Fin.ext (by dsimp only [a]; simp only [Fin.val_succ]; omega)
      have ha : a.val + 1 = j.val := by dsimp only [a]; omega
      have heOwner : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) a.val = i := by
        apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner_unique
        · have h := a.isLt; omega
        · omega
        · omega
      have hePos : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeInnerEdge u v k c.1 a).succ =
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k c.1 i z := by
        apply Fin.ext
        simp only [Fin.val_succ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeInnerEdge_val, heOwner,
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition_val]
        omega
      have hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c) a ≤ rank := by
        change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c) j ≤ rank.val at hl
        rw [hja, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_lo_succ] at hl
        exact hl
      have hv := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k).monotone hc
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut_vertices] at hv
      rw [← hePos, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_lo_succ]
      exact hv
  · by_cases hzlast : z.val + 1 = (c.1.val i).val
    · have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_at_occurrence u v k c.1 i
      change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val + 1) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val +
          (c.1.val i).val at hs
      have hePos : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k c.1 i z =
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeLastPosition u v k c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i) := by
        apply Fin.ext
        change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val + z.val =
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k c.1 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val + 1) - 1
        omega
      rw [hePos, ← houter.2]
      exact hvertex.2
    · let a : Fin (n + e) := ⟨j.val, by have ha := j.isLt; omega⟩
      have hja : j = a.castSucc := Fin.ext rfl
      have ha : a.val = j.val := rfl
      have heOwner : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k) a.val = i := by
        apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner_unique
        · have h := a.isLt; omega
        · omega
        · omega
      have hePos : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeInnerEdge u v k c.1 a).castSucc =
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k c.1 i z := by
        apply Fin.ext
        simp only [Fin.val_castSucc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeInnerEdge_val, heOwner,
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition_val]
        omega
      have hc : rank ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c) a := by
        change rank.val ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c) j at hr
        rw [hja] at hr
        exact hr
      have hv := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k).monotone hc
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut_vertices] at hv
      rw [← hePos]
      exact hv

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
