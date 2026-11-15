module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeRemainingActiveInversions
public import SerrePositivity.EInfinity.SimplexCuts.CompositeInsertedInversionSum
public import SerrePositivity.EInfinity.SimplexCuts.InsertionColorSumDecomposition

/-!
# 元の合成逆転指数を二つの交差和へ分ける

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
同じ色対の有限和を四つへ分け、残り色同士と挿入色同士を元の切断へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の合成逆転指数は、外側残り色対・二方向の交差・内側指数の和（BF §2.2.6）。 -/
lemma positiveComposite_permutationExponent_color_decomposition {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    let δ := positiveCompositeOuterCut u v k c
    let ε := positiveCompositeInnerCut u v k c
    let w := (positiveCompositeCutWord u v k c.1).val
    let uPos := (positiveWord u).val
    permutationExponent c.2 w =
      (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : {b : Fin (m + 1) // b ≠ k},
        ∑ x : ↥(colorPositions δ uPos a.val), ∑ y : ↥(colorPositions δ uPos b.val),
        if x.val ∈ activeVertexPositions δ uPos ∧ y.val ∈ activeVertexPositions δ uPos then
          IntervalCuts.positionInversionTerm (label δ uPos) x.val y.val else 0) +
      (∑ a : {a : Fin (m + 1) // a ≠ k}, ∑ b : Fin (n + 1),
        ∑ x : ↥(colorPositions c.2 w (BarrattEccles.remainingPosition m (n + 1) k a)),
        ∑ y : ↥(colorPositions c.2 w (BarrattEccles.insertedPosition m (n + 1) k b)),
        if x.val ∈ activeVertexPositions c.2 w ∧ y.val ∈ activeVertexPositions c.2 w then
          IntervalCuts.positionInversionTerm (label c.2 w) x.val y.val else 0) +
      (∑ a : Fin (n + 1), ∑ b : {b : Fin (m + 1) // b ≠ k},
        ∑ x : ↥(colorPositions c.2 w (BarrattEccles.insertedPosition m (n + 1) k a)),
        ∑ y : ↥(colorPositions c.2 w (BarrattEccles.remainingPosition m (n + 1) k b)),
        if x.val ∈ activeVertexPositions c.2 w ∧ y.val ∈ activeVertexPositions c.2 w then
          IntervalCuts.positionInversionTerm (label c.2 w) x.val y.val else 0) +
      permutationExponent ε (positiveWord v).val := by
  dsimp only
  rw [permutationExponent_eq_active_inversions, positionInversionCount_eq_sum_color_pairs]
  rw [sum_insertion_position_pairs m (n + 1) k]
  simp_rw [positiveComposite_remaining_active_inversion_sum]
  rw [positiveComposite_inserted_inversion_sum]

end SerrePositivity.EInfinity.SimplexCuts
