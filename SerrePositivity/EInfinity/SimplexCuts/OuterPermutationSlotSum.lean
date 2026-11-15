module

public import SerrePositivity.EInfinity.SimplexCuts.WordColorInversionSums
public import SerrePositivity.EInfinity.SimplexCuts.SlotColorPairSums
public import SerrePositivity.EInfinity.SimplexCuts.SlotCrossWordPositionSums
public import SerrePositivity.EInfinity.SimplexCuts.WeightedWordInversionPairs

/-!
# 元の外側逆転指数と指定色の交差和

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
同じ全色対の和を分け、元の指定色を含む対を同じ出現番号で読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の逆転指数は、残り色対と同じ指定色の交差和（BF §2.2.6）。 -/
lemma positiveWord_permutationExponent_with_slot {m d q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (k : Fin (m + 1)) (s : Cut (m + d) q) :
    let w := (positiveWord u).val
    permutationExponent s w =
      (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : {b : Fin (m + 1) // b ≠ k},
        ∑ p : ↥(Surjection.occurrences w a.val), ∑ h : ↥(Surjection.occurrences w b.val),
        if p.val < h.val ∧ w h.val < w p.val then
          intervalLength s w p.val * intervalLength s w h.val else 0) +
      ∑ p : {p : Fin (m + d + 1) // w p ≠ k},
        ∑ i : Fin (Surjection.occurrenceCount u.val k),
        (IntervalCuts.positionInversionTerm w p.val (positiveOccurrencePosition u k i) +
          IntervalCuts.positionInversionTerm w (positiveOccurrencePosition u k i) p.val) *
          intervalLength s w p.val * intervalLength s w (positiveOccurrencePosition u k i) := by
  dsimp only
  have ho := permutationExponent_eq_sum_occurrence_pairs s (positiveWord u).val
  rw [sum_position_pairs_with_slot m k] at ho
  have hd : (∑ p : ↥(Surjection.occurrences (positiveWord u).val k),
      ∑ h : ↥(Surjection.occurrences (positiveWord u).val k),
      if p.val < h.val ∧ (positiveWord u).val h.val < (positiveWord u).val p.val then
        intervalLength s (positiveWord u).val p.val *
          intervalLength s (positiveWord u).val h.val else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    apply Finset.sum_eq_zero
    intro h _
    have hp := (Finset.mem_filter.mp p.property).2
    have hh := (Finset.mem_filter.mp h.property).2
    simp only [hp, hh, lt_self_iff_false, and_false, ite_false]
  simp only [hd, Nat.add_zero] at ho
  have hc := positiveWord_slot_cross_position_sum u k
    (fun p h => if p < h ∧ (positiveWord u).val h < (positiveWord u).val p then
      intervalLength s (positiveWord u).val p * intervalLength s (positiveWord u).val h else 0)
  simp_rw [weighted_word_inversionPair_eq s (positiveWord u).val] at hc
  omega

end SerrePositivity.EInfinity.SimplexCuts
