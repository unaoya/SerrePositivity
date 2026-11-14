module

public import SerrePositivity.EInfinity.Surjection.AdjacentDeletions

/-!
# 退化した一文字削除の隣接する二色

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
非退化な元の語の削除が退化する場合、消した位置の両隣だけが同じ色になる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C207：退化した削除の同色対は、消した元の位置をちょうど挟む。 -/
lemma erased_word_degenerate_neighbors {m r : ℕ} (v : Surjection.Word r (m + 2))
    (a : Fin (m + 2)) (h : ¬Surjection.Nondegenerate (Surjection.erase v.val a)) :
    ∃ i j : Fin (m + 2), i.val + 1 = a.val ∧ a.val + 1 = j.val ∧ v.val i = v.val j := by
  obtain ⟨i, j, hij, he⟩ : ∃ i j : Fin (m + 1), i.val + 1 = j.val ∧
      Surjection.erase v.val a i = Surjection.erase v.val a j := by
    simpa only [Surjection.Nondegenerate, not_forall, not_imp, ne_eq, not_not, exists_prop] using h
  have hskip : (a.succAbove i).val + 1 ≠ (a.succAbove j).val := by
    intro hs
    exact v.nondegenerate _ _ hs he
  rw [Surjection.succAbove_val_eq, Surjection.succAbove_val_eq] at hskip
  have hleft : i.val + 1 = a.val ∧ j.val = a.val := by
    by_cases hi : i.val < a.val <;> by_cases hj : j.val < a.val <;>
      simp only [hi, hj, ite_true, ite_false] at hskip <;> omega
  refine ⟨a.succAbove i, a.succAbove j, ?_, ?_, he⟩
  · rw [Surjection.succAbove_val_eq, ite_eq_left (by omega)]
    exact hleft.1
  · rw [Surjection.succAbove_val_eq, ite_eq_right (by omega)]
    omega

end SerrePositivity.EInfinity.SimplexCuts
