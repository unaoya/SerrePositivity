module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointWeights

/-!
# 一点削除の前後の元の整数のBF符号

Berger–Fresse §2.2.4・§2.2.6、M14 L12a、報告 §327。
零の区間重みを有限和から除き、同じ元の整数の指数を厳密に比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 唯一の出現の削除は、元の位置指数を保つ（BF §2.2.4）。 -/
lemma positionExponent_erase_unique_point {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (p : Fin (m + 2))
    (h : hi s p = lo s p) (hu : ∀ j, v j = v p → j = p) :
    positionExponent (nullaryPointEraseCut s p) (Surjection.erase v p) = positionExponent s v := by
  unfold positionExponent
  rw [Fin.sum_univ_succAbove _ p]
  simp only [not_caesura_of_unique v p hu, ite_false, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp only [caesura_erase_unique v p hu i, (nullaryPointEraseCut_endpoints s p h i).2]

/-- 唯一の出現の削除は、元の逆転指数を保つ（BF §2.2.4）。 -/
lemma permutationExponent_erase_unique_point {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (p : Fin (m + 2))
    (h : hi s p = lo s p) (hu : ∀ j, v j = v p → j = p) :
    permutationExponent (nullaryPointEraseCut s p) (Surjection.erase v p) =
      permutationExponent s v := by
  unfold permutationExponent
  rw [Fin.sum_univ_succAbove _ p]
  have hp := intervalLength_unique_point s v p h hu
  simp only [hp, zero_mul, ite_self, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succAbove _ p]
  simp only [hp, mul_zero, ite_self, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Surjection.erase_apply, (Fin.strictMono_succAbove p).lt_iff_lt,
    intervalLength_erase_unique_point s v p h hu]

/-- 一点削除の前後で、元の整数のBF符号は厳密に同じ（BF §2.2.6）。 -/
lemma cutSign_erase_unique_point {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (p : Fin (m + 2))
    (h : hi s p = lo s p) (hu : ∀ j, v j = v p → j = p) :
    cutSign (nullaryPointEraseCut s p) (Surjection.erase v p) = cutSign s v := by
  simp only [cutSign, positionExponent_erase_unique_point s v p h hu,
    permutationExponent_erase_unique_point s v p h hu]

end SerrePositivity.EInfinity.SimplexCuts
