module

public import SerrePositivity.EInfinity.SimplexCuts.ColorPairWeightedInversions
public import SerrePositivity.EInfinity.SimplexCuts.RemainingInversionSums

/-!
# 元の残り色の活動逆転和の一致

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
同じ重み付き逆転和を経由し、元の活動頂点の色対の有限和を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ残り色の活動逆転和は元の外側切断の和（BF §2.2.6）。 -/
lemma positiveComposite_remaining_active_inversion_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (a b : {a : Fin (m + 1) // a ≠ k}) :
    (∑ x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
        (BarrattEccles.remainingPosition m (n + 1) k a)),
      ∑ y : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
        (BarrattEccles.remainingPosition m (n + 1) k b)),
      if x.val ∈ activeVertexPositions c.2 (positiveCompositeCutWord u v k c.1).val ∧
          y.val ∈ activeVertexPositions c.2 (positiveCompositeCutWord u v k c.1).val then
        IntervalCuts.positionInversionTerm (label c.2 (positiveCompositeCutWord u v k c.1).val)
          x.val y.val else 0) =
    (∑ x : ↥(colorPositions (positiveCompositeOuterCut u v k c) (positiveWord u).val a.val),
      ∑ y : ↥(colorPositions (positiveCompositeOuterCut u v k c) (positiveWord u).val b.val),
      if x.val ∈ activeVertexPositions (positiveCompositeOuterCut u v k c) (positiveWord u).val ∧
          y.val ∈ activeVertexPositions (positiveCompositeOuterCut u v k c) (positiveWord u).val
        then IntervalCuts.positionInversionTerm
          (label (positiveCompositeOuterCut u v k c) (positiveWord u).val) x.val y.val else 0) := by
  have h := remainingWordPositionOrderIso_inversion_sum u v k c a b
  rw [weighted_color_inversion_sum_eq_active
    (positiveCompositeOuterCut u v k c) (positiveWord u).val a.val b.val,
    weighted_color_inversion_sum_eq_active c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.remainingPosition m (n + 1) k a)
      (BarrattEccles.remainingPosition m (n + 1) k b)] at h
  exact h.symm

end SerrePositivity.EInfinity.SimplexCuts
