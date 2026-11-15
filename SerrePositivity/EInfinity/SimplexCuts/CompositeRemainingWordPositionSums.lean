module

public import SerrePositivity.EInfinity.SimplexCuts.OccurrenceFiberSums
public import SerrePositivity.EInfinity.SimplexCuts.RemainingWordPositions

/-!
# 元の残り色の全位置の和

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の C452。
既存の全出現の同じ順序同値で、元の残り位置へ再添字付けする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 残り色の全出現の和は、同じ元の残り位置の和（BF §2.2.6）。 -/
lemma positiveComposite_remaining_wordPosition_sum {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (F : Fin (m + n + (d + e) + 1) → ℕ) :
    (∑ a : {a : Fin (m + 1) // a ≠ k},
      ∑ h : ↥(Surjection.occurrences (positiveCompositeCutWord u v k r).val
        (BarrattEccles.remainingPosition m (n + 1) k a)), F h.val) =
      ∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
        F (compositeFirstPosition u v k r p.val) := by
  calc
    _ = ∑ a : {a : Fin (m + 1) // a ≠ k},
        ∑ p : ↥(Surjection.occurrences (positiveWord u).val a.val),
          F (compositeFirstPosition u v k r p.val) := by
      apply Finset.sum_congr rfl
      intro a _
      symm
      apply Fintype.sum_equiv (remainingWordPositionOrderIso u v k r a).toEquiv
      intro p
      rfl
    _ = _ := sum_non_slot_occurrences (positiveWord u).val k
      (fun p => F (compositeFirstPosition u v k r p))

end SerrePositivity.EInfinity.SimplexCuts
