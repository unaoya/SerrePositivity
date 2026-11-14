module

public import SerrePositivity.EInfinity.SimplexCuts.RemainingWeightedInversions

/-!
# 元の残り色の全出現位置で数えた逆転和

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
既存の同じ全出現の順序同値により、元の重み付き寄与の二重和を再添字付けする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ全出現の同値は、残り色の重み付き逆転和を保つ（BF §2.2.6）。 -/
lemma remainingWordPositionOrderIso_inversion_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (a b : {a : Fin (m + 1) // a ≠ k}) :
    (∑ p : ↥(Surjection.occurrences (positiveWord u).val a.val),
      ∑ p' : ↥(Surjection.occurrences (positiveWord u).val b.val),
      if p.val < p'.val ∧ (positiveWord u).val p'.val < (positiveWord u).val p.val then
        intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p.val *
          intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p'.val else 0) =
    (∑ p : ↥(Surjection.occurrences (positiveCompositeCutWord u v k c.1).val
        (BarrattEccles.remainingPosition m (n + 1) k a)),
      ∑ p' : ↥(Surjection.occurrences (positiveCompositeCutWord u v k c.1).val
        (BarrattEccles.remainingPosition m (n + 1) k b)),
      if p.val < p'.val ∧ (positiveCompositeCutWord u v k c.1).val p'.val <
          (positiveCompositeCutWord u v k c.1).val p.val then
        intervalLength c.2 (positiveCompositeCutWord u v k c.1).val p.val *
          intervalLength c.2 (positiveCompositeCutWord u v k c.1).val p'.val else 0) := by
  apply Fintype.sum_equiv (remainingWordPositionOrderIso u v k c.1 a).toEquiv
  intro p
  apply Fintype.sum_equiv (remainingWordPositionOrderIso u v k c.1 b).toEquiv
  intro p'
  have hp : (positiveWord u).val p.val ≠ k := by
    have ha := (Finset.mem_filter.mp p.property).2
    exact fun h => a.property (ha.symm.trans h)
  have hp' : (positiveWord u).val p'.val ≠ k := by
    have hb := (Finset.mem_filter.mp p'.property).2
    exact fun h => b.property (hb.symm.trans h)
  exact (positiveComposite_remaining_inversionTerm u v k c p.val p'.val hp hp').symm

end SerrePositivity.EInfinity.SimplexCuts
