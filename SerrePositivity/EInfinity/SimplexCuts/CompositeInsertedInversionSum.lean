module

public import SerrePositivity.EInfinity.SimplexCuts.InsertedColorInversions
public import SerrePositivity.EInfinity.SimplexCuts.ColorInversionSums

/-!
# 合成切断の挿入色の逆転和は同じ内側指数

Berger–Fresse §2.2.6、M14 L12a の C452。
指定した色別同値による有限和を、内側切断の元の重み付き逆転指数に結ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 全挿入色どうしの活動逆転和は元の内側指数（BF §2.2.4・6）。 -/
lemma positiveComposite_inserted_inversion_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    (∑ b : Fin (n + 1), ∑ b' : Fin (n + 1),
      ∑ x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
        (BarrattEccles.insertedPosition m (n + 1) k b)),
      ∑ y : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
        (BarrattEccles.insertedPosition m (n + 1) k b')),
      if x.val ∈ activeVertexPositions c.2 (positiveCompositeCutWord u v k c.1).val ∧
          y.val ∈ activeVertexPositions c.2 (positiveCompositeCutWord u v k c.1).val then
        IntervalCuts.positionInversionTerm (label c.2 (positiveCompositeCutWord u v k c.1).val)
          x.val y.val else 0) =
      permutationExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val := by
  rw [permutationExponent_eq_active_inversions, positionInversionCount_eq_sum_color_pairs]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro b' _
  exact insertedColorPathOrderIso_active_inversion_sum u v k c b b'

end SerrePositivity.EInfinity.SimplexCuts
