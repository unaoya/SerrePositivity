module

public import SerrePositivity.EInfinity.SimplexCuts.CompositePermutationCrossBalance
public import SerrePositivity.EInfinity.SimplexCuts.CompositeOtherActivePrefix
public import Mathlib.Algebra.BigOperators.ModEq

/-!
# 元の合成逆転指数と内外指数・B_i・Pのmod 2

Berger–Fresse §1.2.5・§2.2.4・§2.2.6、M14 L12a の C452。
元の整数の釣り合いへ、同じ先行他色数と前方総次数の合同を成分ごとに掛けて足す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の逆転指数は、内外指数と同じB_i・Pの補正に合同（BF §2.2.6）。 -/
lemma positiveComposite_permutationExponent_modeq {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (_h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
    Nat.ModEq 2 (permutationExponent c.2 (positiveCompositeCutWord u v k c.1).val)
      (permutationExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val +
        permutationExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val +
        (∑ i, Surjection.segmentDegree v.val c.1 i *
          (positiveCompositeOtherActivePrefix u v k c i +
            positiveNestedPrefixDegree u k (positiveCompositeOuterCut u v k c)))) := by
  have he := positiveComposite_permutationExponent_cross_balance u v k c
  dsimp only at he
  rw [he]
  apply Nat.ModEq.add_left
  apply Nat.ModEq.sum
  intro i _
  exact (positiveComposite_crossWeight_modeq u v k c i).mul_left
    (Surjection.segmentDegree v.val c.1 i)

end SerrePositivity.EInfinity.SimplexCuts
