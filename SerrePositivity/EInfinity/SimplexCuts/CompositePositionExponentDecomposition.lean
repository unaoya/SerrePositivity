module

public import SerrePositivity.EInfinity.SimplexCuts.CompositePositionTerms
public import SerrePositivity.EInfinity.SimplexCuts.CompositeWordPositionSums
public import SerrePositivity.EInfinity.SimplexCuts.PositiveWordPositionSums

/-!
# 元の合成位置指数を外側と部分語内部の和へ分ける

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
同じ全位置の和を分け、残り位置と部分語末尾を元の外側指数へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の合成位置指数は、外側指数と同じ部分語内部の区切り高さの和（BF §2.2.6）。 -/
lemma positiveComposite_positionExponent_decomposition {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    positionExponent c.2 (positiveCompositeCutWord u v k c.1).val =
      positionExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val +
      ∑ i : Fin (Surjection.occurrenceCount u.val k), ∑ z : Fin ((c.1.val i).val - 1),
        if Surjection.Caesura v.val
            ⟨c.1.start i + z.val, by have hb := c.1.start_add_length_le i; have hz := z.isLt; omega⟩
        then hi c.2 (positiveCompositeSegmentPosition u v k c.1 i
          ⟨z.val, by have hz := z.isLt; omega⟩) else 0 := by
  have hg := positiveComposite_wordPosition_sum u v k c.1
    (fun p => if Surjection.Caesura (positiveCompositeCutWord u v k c.1).val p
      then hi c.2 p else 0)
  change positionExponent c.2 (positiveCompositeCutWord u v k c.1).val = _ at hg
  have hr :
      (∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
        if Surjection.Caesura (positiveCompositeCutWord u v k c.1).val
            (compositeFirstPosition u v k c.1 p.val) then
          hi c.2 (compositeFirstPosition u v k c.1 p.val) else 0) =
      ∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
        if Surjection.Caesura (positiveWord u).val p.val then
          hi (positiveCompositeOuterCut u v k c) p.val else 0 := by
    apply Finset.sum_congr rfl
    intro p _
    exact positiveComposite_remaining_positionTerm u v k c p.val p.property
  simp only [hr] at hg
  simp_rw [positiveComposite_segment_positionTerm_sum u v k c] at hg
  rw [Finset.sum_add_distrib] at hg
  have ho := positiveWord_position_sum u k
    (fun p => if Surjection.Caesura (positiveWord u).val p then
      hi (positiveCompositeOuterCut u v k c) p else 0)
  change positionExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val = _ at ho
  omega

end SerrePositivity.EInfinity.SimplexCuts
