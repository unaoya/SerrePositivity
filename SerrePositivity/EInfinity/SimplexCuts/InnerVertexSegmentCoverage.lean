module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentInnerRanks

/-!
# 元の内側頂点の位置は同じ外側順位の部分語に属する

Berger–Fresse §2.2.6、M14 L12a のC451の逆方向。
元の内側Cutの両端と外側順位の両端を、同じ分割の開始・終了位置で比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ内側頂点と外側順位が指定する部分語は元の内側位置を含む（BF §2.2.6）。 -/
lemma positiveCompositeInnerPosition_segment_covered {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (a : Fin (n + e + 1))
    (rank : Fin (outputDegree (positiveCompositeOuterCut u v k c) (positiveWord u) k + 1))
    (hm : rank ∈ colorIntervalRanks (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i))
    (hl : lo (positiveCompositeInnerCut u v k c) a ≤ rank.val)
    (hr : rank.val ≤ hi (positiveCompositeInnerCut u v k c) a) :
    c.1.start i ≤ a.val ∧ a.val < c.1.start i + (c.1.val i).val := by
  have hf : (colorIntervalFirst (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i)).val ≤ rank.val :=
    (colorIntervalRanks _ _ _ _).min'_le rank hm
  have ht : rank.val ≤ (colorIntervalLast (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i)).val :=
    (colorIntervalRanks _ _ _ _).le_max' rank hm
  have hp := c.1.positive (by omega : 0 < (n + 1) + e) i
  have hb := c.1.start_add_length_le i
  have ha := a.isLt
  constructor
  · by_contra hn
    have hn' : a.val < c.1.start i := lt_of_not_ge hn
    let b : Fin (n + e) := ⟨a.val, by omega⟩
    have he : a = b.castSucc := Fin.ext rfl
    have hc : rank.val ≤ (cutHeights (positiveCompositeInnerCut u v k c) b).val := by
      rw [he] at hr
      exact hr
    have hfirst : colorIntervalFirst (positiveCompositeOuterCut u v k c) (positiveWord u) k
        (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i) ≤
        cutHeights (positiveCompositeInnerCut u v k c) b := le_trans hf hc
    have hstart := ((positiveCompositeInnerCut_rank_bounds_iff u v k c b i).1).mp hfirst
    change c.1.start i ≤ a.val at hstart
    omega
  · by_contra hn
    have hn' : c.1.start i + (c.1.val i).val ≤ a.val := le_of_not_gt hn
    let b : Fin (n + e) := ⟨a.val - 1, by omega⟩
    have he : a = b.succ := Fin.ext (by dsimp only [b]; simp only [Fin.val_succ]; omega)
    have hc : (cutHeights (positiveCompositeInnerCut u v k c) b).val ≤ rank.val := by
      rw [he, ← hi_eq_lo_succ] at hl
      exact hl
    have hlast : cutHeights (positiveCompositeInnerCut u v k c) b ≤
        colorIntervalLast (positiveCompositeOuterCut u v k c) (positiveWord u) k
          (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i) :=
      le_trans hc ht
    have hend := ((positiveCompositeInnerCut_rank_bounds_iff u v k c b i).2).mp hlast
    change a.val - 1 + 1 < c.1.start i + (c.1.val i).val at hend
    omega

end SerrePositivity.EInfinity.SimplexCuts
