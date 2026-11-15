module

public import SerrePositivity.EInfinity.SimplexCuts.NestedCutCoefficients
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Ring.Commute

/-!
# 元の符号指数のmod 2の照合から同じ整数係数へ戻す

Berger–Fresse §1.2.5・§2.2.4–6、M14 L12a のC452の係数移送。
肝心の指数の比較は入力に露出させ、元の二つの係数移動とcutSignを保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C452の同じ指数の比較を、元の整数係数の等式として読む（BF §2.2.6）。 -/
lemma positiveCompositeCutCoefficient_eq_nested_of_modeq {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nat.ModEq 2
      (Surjection.compositionExponent u v k c.1 +
        (permutationExponent c.2 (positiveCompositeCutWord u v k c.1).val +
          positionExponent c.2 (positiveCompositeCutWord u v k c.1).val))
      ((d * e + e * positiveNestedPrefixDegree u k (positiveCompositeOuterCut u v k c)) +
        (permutationExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val +
          positionExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val) +
        (permutationExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val +
          positionExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val))) :
    Surjection.compositionSign u v k c.1 * cutSign c.2 (positiveCompositeCutWord u v k c.1).val =
      positiveNestedCutCoefficient u v k (positiveCompositeNestedMap u v k c) := by
  let x := Surjection.compositionExponent u v k c.1 +
    (permutationExponent c.2 (positiveCompositeCutWord u v k c.1).val +
      positionExponent c.2 (positiveCompositeCutWord u v k c.1).val)
  let y := (d * e + e * positiveNestedPrefixDegree u k (positiveCompositeOuterCut u v k c)) +
    (permutationExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val +
      positionExponent (positiveCompositeOuterCut u v k c) (positiveWord u).val) +
    (permutationExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val +
      positionExponent (positiveCompositeInnerCut u v k c) (positiveWord v).val)
  have he : x % 2 = y % 2 := h
  have hs : (-1 : ℤ) ^ x = (-1 : ℤ) ^ y := by
    rw [neg_one_pow_eq_pow_mod_two x, neg_one_pow_eq_pow_mod_two y]
    exact congrArg (fun n : ℕ => (-1 : ℤ) ^ n) he
  simpa only [Surjection.compositionSign, cutSign, positiveNestedCutCoefficient,
    positiveCompositeNestedMap, ← pow_add, x, y] using hs

end SerrePositivity.EInfinity.SimplexCuts
