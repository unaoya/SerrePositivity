module

public import SerrePositivity.EInfinity.SimplexCuts.IntervalBoundaryGlue
public import SerrePositivity.EInfinity.SimplexCuts.IntervalSingletons
public import Mathlib.Algebra.BigOperators.Fin

/-!
# 元の連続区間の幅の和と両端

Berger–Fresse §2.2.3・§2.2.6、M14 L12a の C452。
隣接する区間の共有端点を消し、同じ両端の高さの差を読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の連続区間の幅の和は同じ両端の高さの差（BF §2.2.3・6）。 -/
lemma sum_consecutive_intervalWidths {m q : ℕ} (s : Cut m q)
    (a L : ℕ) (h : a + L < m + 1) :
    (∑ z : Fin (L + 1), (hi s ⟨a + z.val, by have hz := z.isLt; omega⟩ -
      lo s ⟨a + z.val, by have hz := z.isLt; omega⟩)) +
      lo s ⟨a, by omega⟩ = hi s ⟨a + L, h⟩ := by
  induction L with
  | zero =>
    simp only [Nat.add_zero]
    exact Nat.sub_add_cancel (lo_le_hi s _)
  | succ L ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hp := ih (by omega : a + L < m + 1)
    have hg := hi_eq_lo_succ s (⟨a + L, by omega⟩ : Fin m)
    change hi s ⟨a + L, by omega⟩ = lo s ⟨a + (L + 1), h⟩ at hg
    have hle := lo_le_hi s (⟨a + (L + 1), h⟩ : Fin (m + 1))
    rw [← hg] at hle ⊢
    omega

end SerrePositivity.EInfinity.SimplexCuts
