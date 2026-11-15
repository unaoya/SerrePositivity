module

public import SerrePositivity.EInfinity.SimplexCuts.RemainingCaesuraWeights
public import SerrePositivity.EInfinity.IntervalCuts.RemainingPositionOrder

/-!
# 元の残り色の重み付き逆転寄与

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
同じ合成位置の順序・色番号・区間長を保って、残り色の対の寄与を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の残り色の位置対の重み付き逆転寄与は変わらない（BF §2.2.4・6）。 -/
lemma positiveComposite_remaining_inversionTerm {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (p p' : Fin (m + d + 1))
    (hp : (positiveWord u).val p ≠ k) (hp' : (positiveWord u).val p' ≠ k) :
    (if compositeFirstPosition u v k c.1 p < compositeFirstPosition u v k c.1 p' ∧
        (positiveCompositeCutWord u v k c.1).val (compositeFirstPosition u v k c.1 p') <
          (positiveCompositeCutWord u v k c.1).val (compositeFirstPosition u v k c.1 p) then
      intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
          (compositeFirstPosition u v k c.1 p) *
        intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
          (compositeFirstPosition u v k c.1 p') else 0) =
    (if p < p' ∧ (positiveWord u).val p' < (positiveWord u).val p then
      intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p *
        intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p' else 0) := by
  simp only [(compositeFirstPosition_strictMono u v k c.1).lt_iff_lt,
    positiveCompositeFirstPosition_label u v k c.1 p hp,
    positiveCompositeFirstPosition_label u v k c.1 p' hp',
    IntervalCuts.remainingPosition_lt_iff,
    positiveComposite_remaining_intervalLength u v k c p hp,
    positiveComposite_remaining_intervalLength u v k c p' hp']

end SerrePositivity.EInfinity.SimplexCuts
