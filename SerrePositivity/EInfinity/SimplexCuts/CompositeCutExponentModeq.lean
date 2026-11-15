module

public import SerrePositivity.EInfinity.SimplexCuts.CompositePositionExponentBalance
public import SerrePositivity.EInfinity.SimplexCuts.CompositePermutationModeq
public import SerrePositivity.EInfinity.SimplexCuts.CompositionExponentComplement

/-!
# 元の合成切断の符号指数のmod 2

Berger–Fresse §1.2.5・§2.2.4・§2.2.6、M14 L12a の C452。
報告 §243・§253 の元の指数を、同じ位置・逆転・合成指数の等式から照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の合成切断の全符号指数は、元の二段の指数に合同（BF §2.2.6）。 -/
lemma positiveCompositeCut_exponent_modeq {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
    Nat.ModEq 2
      (Surjection.compositionExponent u v k c.1 +
        (permutationExponent c.2 (positiveCompositeCutWord u v k c.1).val +
          positionExponent c.2 (positiveCompositeCutWord u v k c.1).val))
      ((d * e + e * positiveNestedPrefixDegree u k (positiveCompositeOuterCut u v k c)) +
        (permutationExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val +
          positionExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val) +
        (permutationExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val +
          positionExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val)) := by
  have hp := positiveComposite_positionExponent_balance u v k c h
  have hc := compositionExponent_add_prefixRanks u v k c.1
  have hi := positiveComposite_permutationExponent_modeq u v k c h
  have hs : (∑ i, Surjection.segmentDegree v.val c.1 i *
      (positiveCompositeOtherActivePrefix u v k c i +
        positiveNestedPrefixDegree u k (positiveCompositeOuterCut u v k c))) =
      (∑ i, Surjection.segmentDegree v.val c.1 i *
        positiveCompositeOtherActivePrefix u v k c i) +
      e * positiveNestedPrefixDegree u k (positiveCompositeOuterCut u v k c) := by
    simp_rw [Nat.mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul,
      Surjection.sum_segmentDegree v c.1 (Surjection.occurrenceCount_pos u k)]
  rw [hs] at hi
  dsimp only [Nat.ModEq] at hi ⊢
  omega

end SerrePositivity.EInfinity.SimplexCuts
