module

public import SerrePositivity.EInfinity.SimplexCuts.OccurrenceCaesuraTransport
public import SerrePositivity.EInfinity.SimplexCuts.RemainingWordPositions

/-!
# 元の残り色の区切りと符号の区間長

Berger–Fresse §1.2.2・§2.2.4–6、M14 L12a のC452。
元の全出現位置と同じ両端を使い、CaesuraとintervalLengthを変更せずに読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 残り色の元の区切りは、同じ合成位置で保たれる（BF §2.2.4）。 -/
lemma positiveComposite_remaining_caesura_iff {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k) :
    Surjection.Caesura (positiveCompositeCutWord u v k r).val
        (compositeFirstPosition u v k r p) ↔ Surjection.Caesura (positiveWord u).val p := by
  let a : {a : Fin (m + 1) // a ≠ k} := ⟨(positiveWord u).val p, hp⟩
  let p' : ↥(Surjection.occurrences (positiveWord u).val a.val) :=
    ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  exact caesura_iff_of_occurrenceOrderIso _ _ _ _ (remainingWordPositionOrderIso u v k r a) p'

/-- 残り色の元の区間長は、同じ合成位置で外側の区間長と一致（BF §2.2.4–6）。 -/
lemma positiveComposite_remaining_intervalLength {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k) :
    intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
        (compositeFirstPosition u v k c.1 p) =
      intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p := by
  unfold intervalLength
  rw [(positiveCompositeOuterCut_endpoints u v k c p).1,
    (positiveCompositeOuterCut_endpoints u v k c p).2]
  rw [← compositeFirstPosition_eq_last_of_non_slot u v k c.1 p hp]
  simp only [positiveComposite_remaining_caesura_iff u v k c.1 p hp]

end SerrePositivity.EInfinity.SimplexCuts
