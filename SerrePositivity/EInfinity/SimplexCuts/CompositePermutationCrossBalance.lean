module

public import SerrePositivity.EInfinity.SimplexCuts.CompositePermutationColorDecomposition
public import SerrePositivity.EInfinity.SimplexCuts.ColorPairWeightedInversions
public import SerrePositivity.EInfinity.SimplexCuts.CompositeCrossIntervalLengthSums
public import SerrePositivity.EInfinity.SimplexCuts.OuterPermutationSlotSum

/-!
# 元の合成逆転指数と成分次数の交差補正

Berger–Fresse §1.2.5・§2.2.4・§2.2.6、M14 L12a の C452。
同じ残り色対と元の外側交差を合わせ、成分次数の非負の補正を残す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の合成逆転指数は、内外指数と同じ交差補正の和（BF §2.2.6）。 -/
lemma positiveComposite_permutationExponent_cross_balance {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    let δ := positiveCompositeOuterCut u v k c
    let ε := positiveCompositeInnerCut u v k c
    let w := (positiveWord u).val
    permutationExponent c.2 (positiveCompositeCutWord u v k c.1).val =
      permutationExponent δ w + permutationExponent ε (positiveWord v).val +
      ∑ i : Fin (Surjection.occurrenceCount u.val k),
        Surjection.segmentDegree v.val c.1 i *
        (∑ p : {p : Fin (m + d + 1) // w p ≠ k},
          (IntervalCuts.positionInversionTerm w p.val (positiveOccurrencePosition u k i) +
            IntervalCuts.positionInversionTerm w (positiveOccurrencePosition u k i) p.val) *
            intervalLength δ w p.val) := by
  dsimp only
  have hg := positiveComposite_permutationExponent_color_decomposition u v k c
  dsimp only at hg
  simp_rw [← weighted_color_inversion_sum_eq_active
      (positiveCompositeOuterCut u v k c) (positiveWord u).val,
    ← weighted_color_inversion_sum_eq_active c.2 (positiveCompositeCutWord u v k c.1).val] at hg
  have ho := positiveWord_permutationExponent_with_slot u k (positiveCompositeOuterCut u v k c)
  dsimp only at ho
  have hc := positiveComposite_cross_intervalLength_sum u v k c
  dsimp only at hc
  simp_rw [Nat.mul_add, Finset.sum_add_distrib] at hc
  have he :
      (∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
        ∑ i : Fin (Surjection.occurrenceCount u.val k),
        (IntervalCuts.positionInversionTerm (positiveWord u).val p.val
            (positiveOccurrencePosition u k i) +
          IntervalCuts.positionInversionTerm (positiveWord u).val
            (positiveOccurrencePosition u k i) p.val) *
          intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p.val *
          Surjection.segmentDegree v.val c.1 i) =
      ∑ i : Fin (Surjection.occurrenceCount u.val k), Surjection.segmentDegree v.val c.1 i *
        (∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
          (IntervalCuts.positionInversionTerm (positiveWord u).val p.val
              (positiveOccurrencePosition u k i) +
            IntervalCuts.positionInversionTerm (positiveWord u).val
              (positiveOccurrencePosition u k i) p.val) *
            intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p.val) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, Nat.mul_comm]
  rw [he] at hc
  omega

end SerrePositivity.EInfinity.SimplexCuts
