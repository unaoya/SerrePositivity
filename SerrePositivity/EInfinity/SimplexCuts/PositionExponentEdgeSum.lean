module

public import SerrePositivity.EInfinity.SimplexCuts.CutHeights
public import SerrePositivity.EInfinity.SimplexCuts.Signs
public import Mathlib.Algebra.BigOperators.Fin

/-!
# 位置指数を元の水平辺で読む

Berger–Fresse §1.2.5・§2.2.6、M14 L12a の C452。
報告 §289 の同じ有限位置・同じ順位の証明分割。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 末尾に区切りはなく、同じ位置指数は水平辺の高さの和（BF §2.2.6）。 -/
lemma positionExponent_eq_edge_sum {m q r : ℕ} (s : Cut m q)
    (w : Fin (m + 1) → Fin r) :
    positionExponent s w =
      ∑ a : Fin m, if Surjection.Caesura w a.castSucc then (cutHeights s a).val else 0 := by
  have hlast : ¬ Surjection.Caesura w (Fin.last m) := by
    rintro ⟨j, hj, _⟩
    have hb := j.isLt
    change m < j.val at hj
    omega
  unfold positionExponent
  rw [Fin.sum_univ_castSucc]
  simp only [hlast, ↓reduceIte, Nat.add_zero]
  rfl

end SerrePositivity.EInfinity.SimplexCuts
