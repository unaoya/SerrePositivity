module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeInnerRankBounds
public import SerrePositivity.EInfinity.SimplexCuts.FiniteEndpointComparison
public import SerrePositivity.EInfinity.SimplexCuts.CutHeightExchange

/-!
# 元の一段切断から復元する同じ部分語の両端

Berger–Fresse §2.2.6、M14 L12a のC449の証明分割。
同じ有限辺との全比較を使い、元の分割の開始・終了位置へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C449a：同じ順位区間の交換経路の始点は、元の部分語の始点（BF §2.2.6）。 -/
lemma positiveCompositeNestedMap_segmentStart {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    lo (positiveCompositeInnerCut u v k c).exchange
        (colorIntervalFirst (positiveCompositeOuterCut u v k c) (positiveWord u) k
          (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i)) =
      c.1.start i := by
  have hb := c.1.start_add_length_le i
  have hp := c.1.positive (by omega : 0 < (n + 1) + e) i
  apply nat_eq_of_fin_le_iff _ _ (lo_le_q _ _) (by omega : c.1.start i ≤ n + e)
  intro a
  exact (cutHeights_exchange_bounds (positiveCompositeInnerCut u v k c) a _).1.trans
    (positiveCompositeInnerCut_rank_bounds_iff u v k c a i).1

/-- C449b：同じ順位区間の交換経路の終点は、元の部分語の終点（BF §2.2.6）。 -/
lemma positiveCompositeNestedMap_segmentEnd {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    hi (positiveCompositeInnerCut u v k c).exchange
        (colorIntervalLast (positiveCompositeOuterCut u v k c) (positiveWord u) k
          (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i)) =
      c.1.start i + (c.1.val i).val - 1 := by
  have hb := c.1.start_add_length_le i
  apply nat_eq_of_fin_le_iff _ _ (hi_le_q _ _)
    (by omega : c.1.start i + (c.1.val i).val - 1 ≤ n + e)
  intro a
  have h := (cutHeights_exchange_bounds (positiveCompositeInnerCut u v k c) a
    (colorIntervalLast (positiveCompositeOuterCut u v k c) (positiveWord u) k
      (positiveOccurrencePosition u k i) (positiveOccurrencePosition_value u k i))).2.trans
        (positiveCompositeInnerCut_rank_bounds_iff u v k c a i).2
  constructor
  · intro hle
    have hn : ¬a.val + 1 < c.1.start i + (c.1.val i).val :=
      fun hlt => (not_lt_of_ge hle) (h.mpr hlt)
    omega
  · intro hle
    by_contra hnot
    have hr := h.mp (lt_of_not_ge hnot)
    omega

end SerrePositivity.EInfinity.SimplexCuts
