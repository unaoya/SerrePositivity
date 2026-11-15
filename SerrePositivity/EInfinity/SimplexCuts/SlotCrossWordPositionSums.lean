module

public import SerrePositivity.EInfinity.SimplexCuts.PositiveOccurrenceSums
public import SerrePositivity.EInfinity.SimplexCuts.OccurrenceFiberSums

/-!
# 元の指定色を含む二方向の交差和の位置の表示

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の C452。
元の指定色の出現を番号へ戻し、元の残り位置との二方向の対を揃える。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 指定色へ向かう元の全位置対の和を、同じ出現番号で読む（BF §2.2.6）。 -/
lemma positiveWord_remaining_slot_position_sum {m d : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (k : Fin (m + 1))
    (F : Fin (m + d + 1) → Fin (m + d + 1) → ℕ) :
    (∑ a : {a : Fin (m + 1) // a ≠ k},
      ∑ p : ↥(Surjection.occurrences (positiveWord u).val a.val),
      ∑ h : ↥(Surjection.occurrences (positiveWord u).val k), F p.val h.val) =
    ∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
      ∑ i : Fin (Surjection.occurrenceCount u.val k),
        F p.val (positiveOccurrencePosition u k i) := by
  calc
    _ = ∑ a : {a : Fin (m + 1) // a ≠ k},
        ∑ p : ↥(Surjection.occurrences (positiveWord u).val a.val),
        ∑ i : Fin (Surjection.occurrenceCount u.val k),
          F p.val (positiveOccurrencePosition u k i) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro p _
      exact positiveWord_slot_position_sum u k (F p.val)
    _ = _ := sum_non_slot_occurrences (positiveWord u).val k
      (fun p => ∑ i : Fin (Surjection.occurrenceCount u.val k),
        F p (positiveOccurrencePosition u k i))

/-- 指定色を含む両向きの元の交差和を、同じ位置対へ戻す（BF §2.2.6）。 -/
lemma positiveWord_slot_cross_position_sum {m d : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (k : Fin (m + 1))
    (F : Fin (m + d + 1) → Fin (m + d + 1) → ℕ) :
    (∑ a : {a : Fin (m + 1) // a ≠ k},
      ∑ p : ↥(Surjection.occurrences (positiveWord u).val a.val),
      ∑ h : ↥(Surjection.occurrences (positiveWord u).val k), F p.val h.val) +
    (∑ b : {b : Fin (m + 1) // b ≠ k},
      ∑ p : ↥(Surjection.occurrences (positiveWord u).val k),
      ∑ h : ↥(Surjection.occurrences (positiveWord u).val b.val), F p.val h.val) =
    ∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
      ∑ i : Fin (Surjection.occurrenceCount u.val k),
        (F p.val (positiveOccurrencePosition u k i) +
          F (positiveOccurrencePosition u k i) p.val) := by
  have hr : (∑ b : {b : Fin (m + 1) // b ≠ k},
      ∑ p : ↥(Surjection.occurrences (positiveWord u).val k),
      ∑ h : ↥(Surjection.occurrences (positiveWord u).val b.val), F p.val h.val) =
      ∑ h : {h : Fin (m + d + 1) // (positiveWord u).val h ≠ k},
        ∑ i : Fin (Surjection.occurrenceCount u.val k),
          F (positiveOccurrencePosition u k i) h.val := by
    calc
      _ = ∑ b : {b : Fin (m + 1) // b ≠ k},
          ∑ h : ↥(Surjection.occurrences (positiveWord u).val b.val),
          ∑ p : ↥(Surjection.occurrences (positiveWord u).val k), F p.val h.val := by
        apply Finset.sum_congr rfl
        intro b _
        exact Finset.sum_comm
      _ = _ := positiveWord_remaining_slot_position_sum u k (fun h p => F p h)
  rw [positiveWord_remaining_slot_position_sum u k F, hr]
  simp only [Finset.sum_add_distrib]

end SerrePositivity.EInfinity.SimplexCuts
