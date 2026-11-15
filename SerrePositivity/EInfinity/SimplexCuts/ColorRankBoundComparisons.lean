module

public import SerrePositivity.EInfinity.SimplexCuts.ColorRankIntervals

/-!
# 元の色別区間の両端と順位の比較

Berger–Fresse §2.2.6、M14 L12a の左逆の証明分割。
同じ水平座標の区間内の順位を、元の区間の順序で比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C444：元の最初の順位との比較は、元の区間の比較（BF §2.2.6）。 -/
lemma colorIntervalFirst_le_rank_iff {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p p' : Fin (m + 1))
    (_hp : v.val p = a) (hp' : v.val p' = a)
    (j : Fin (outputDegree s v a + 1)) (hj : j ∈ colorIntervalRanks s v a p) :
    colorIntervalFirst s v a p' hp' ≤ j ↔ p' ≤ p := by
  have hfirst := (colorIntervalRanks s v a p').min'_mem
    (colorIntervalRanks_nonempty s v a p' hp')
  constructor
  · intro h
    by_contra hnot
    have hlt := colorIntervalRanks_ordered s v a p p' (lt_of_not_ge hnot) _ _ hj hfirst
    exact (not_le_of_gt hlt) h
  · intro h
    rcases eq_or_lt_of_le h with he | hlt
    · subst p'
      exact (colorIntervalRanks s v a p).min'_le j hj
    · exact le_of_lt (colorIntervalRanks_ordered s v a p' p hlt _ _ hfirst hj)

/-- C445：元の最後の順位との比較は、元の区間の比較（BF §2.2.6）。 -/
lemma rank_le_colorIntervalLast_iff {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p p' : Fin (m + 1))
    (_hp : v.val p = a) (hp' : v.val p' = a)
    (j : Fin (outputDegree s v a + 1)) (hj : j ∈ colorIntervalRanks s v a p) :
    j ≤ colorIntervalLast s v a p' hp' ↔ p ≤ p' := by
  have hlast := (colorIntervalRanks s v a p').max'_mem
    (colorIntervalRanks_nonempty s v a p' hp')
  constructor
  · intro h
    by_contra hnot
    have hlt := colorIntervalRanks_ordered s v a p' p (lt_of_not_ge hnot) _ _ hlast hj
    exact (not_le_of_gt hlt) h
  · intro h
    rcases eq_or_lt_of_le h with he | hlt
    · subst p'
      exact (colorIntervalRanks s v a p).le_max' j hj
    · exact le_of_lt (colorIntervalRanks_ordered s v a p p' hlt _ _ hj hlast)

end SerrePositivity.EInfinity.SimplexCuts
