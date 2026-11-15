module

public import SerrePositivity.EInfinity.SimplexCuts.PositiveOccurrenceSums

/-!
# 元の全位置と残り位置・指定色の出現の和

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の C452。
同じ位置の有限和を二つへ分け、指定色の位置を元の出現番号で読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の全位置の和を、残り位置と同じ指定色の出現番号で読む（BF §2.2.6）。 -/
lemma positiveWord_position_sum {m d : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (k : Fin (m + 1)) (F : Fin (m + d + 1) → ℕ) :
    (∑ p, F p) =
      (∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k}, F p.val) +
      ∑ i : Fin (Surjection.occurrenceCount u.val k), F (positiveOccurrencePosition u k i) := by
  classical
  let e : {p : Fin (m + d + 1) // ¬(positiveWord u).val p ≠ k} ≃
      ↥(Surjection.occurrences (positiveWord u).val k) :=
    Equiv.subtypeEquivRight (fun p => by simp [Surjection.occurrences])
  have he : (∑ p : {p : Fin (m + d + 1) // ¬(positiveWord u).val p ≠ k}, F p.val) =
      ∑ i : Fin (Surjection.occurrenceCount u.val k), F (positiveOccurrencePosition u k i) := by
    calc
      _ = ∑ p : ↥(Surjection.occurrences (positiveWord u).val k), F p.val := by
        apply Fintype.sum_equiv e
        intro p
        rfl
      _ = _ := positiveWord_slot_position_sum u k F
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun p : Fin (m + d + 1) => (positiveWord u).val p ≠ k) F
  simp only [he] at hs
  exact hs.symm

end SerrePositivity.EInfinity.SimplexCuts
