module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointEndpoints
public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointCaesuras

/-!
# 一点削除の前後の区間重み

Berger–Fresse §2.2.4・§2.2.6、M14 L12a、報告 §327。
一度だけ出る削除色の重み零と、元の全区間の重みの一致を読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 唯一の出現の一点区間の重みは零（BF §2.2.6）。 -/
lemma intervalLength_unique_point {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (p : Fin (m + 2))
    (h : hi s p = lo s p) (hu : ∀ j, v j = v p → j = p) : intervalLength s v p = 0 := by
  simp only [intervalLength, h, Nat.sub_self, not_caesura_of_unique v p hu, ite_false,
    Nat.add_zero]

/-- 残る全区間の元のBF重みは変わらない（BF §2.2.4）。 -/
lemma intervalLength_erase_unique_point {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (p : Fin (m + 2))
    (h : hi s p = lo s p) (hu : ∀ j, v j = v p → j = p) (i : Fin (m + 1)) :
    intervalLength (nullaryPointEraseCut s p) (Surjection.erase v p) i =
      intervalLength s v (p.succAbove i) := by
  simp only [intervalLength, (nullaryPointEraseCut_endpoints s p h i).1,
    (nullaryPointEraseCut_endpoints s p h i).2, caesura_erase_unique v p hu i]

end SerrePositivity.EInfinity.SimplexCuts
