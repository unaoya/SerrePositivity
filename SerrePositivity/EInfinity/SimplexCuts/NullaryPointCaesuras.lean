module

public import SerrePositivity.EInfinity.IntervalCuts.GeneralDeletionCaesuras

/-!
# 一度だけ現れる色の削除と区切り

Berger–Fresse §1.2.3・§2.2.6、M14 L12a、報告 §326。
同じraw語の将来出現を削除位置の順序単射で比較する。
-/

@[expose] public section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 唯一の出現は区切りではない（BF §1.2.3）。 -/
lemma not_caesura_of_unique {l r : ℕ} (v : Fin (l + 1) → Fin r) (p : Fin (l + 1))
    (hu : ∀ j, v j = v p → j = p) : ¬ Surjection.Caesura v p := by
  rintro ⟨j, hj, hv⟩
  exact (ne_of_gt hj) (hu j hv)

/-- 唯一の出現の削除は、残る全位置の区切りを保つ（BF §1.2.3）。 -/
lemma caesura_erase_unique {l r : ℕ} (v : Fin (l + 1) → Fin r) (p : Fin (l + 1))
    (hu : ∀ j, v j = v p → j = p) (i : Fin l) :
    Surjection.Caesura (Surjection.erase v p) i ↔ Surjection.Caesura v (p.succAbove i) := by
  rw [IntervalCuts.caesura_erase_iff_witness]
  constructor
  · rintro ⟨j, _, hj, hv⟩
    exact ⟨j, hj, hv⟩
  · rintro ⟨j, hj, hv⟩
    refine ⟨j, ?_, hj, hv⟩
    intro he
    have hp : p.succAbove i = p := hu _ (by simpa only [he] using hv.symm)
    exact Fin.succAbove_ne p i hp

end SerrePositivity.EInfinity.SimplexCuts
