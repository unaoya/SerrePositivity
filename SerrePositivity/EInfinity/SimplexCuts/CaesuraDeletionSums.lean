module

public import SerrePositivity.EInfinity.SimplexCuts.CaesuraVertexDeletion
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# 同じcaesura削除集合の重み付き和

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
既存の一位置削除の集合等式を、位置指数で使う重み付き有限和へ運ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C171：活動位置の削除では、その位置の重みだけを取り除く。 -/
lemma caesura_sum_erase_active {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (a : Fin (N + 1)) (ha : Surjection.Caesura v a) (H : Fin (N + 1) → ℕ) :
    (∑ i ∈ caesuraPositions v, H i) =
      (∑ i ∈ caesuraPositions (Surjection.erase v a), H (a.succAbove i)) + H a := by
  have hm : a ∈ caesuraPositions v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
  rw [← Finset.sum_erase_add (caesuraPositions v) H hm,
    ← caesuraPositions_erase_active_image v a ha]
  congr 1
  exact Finset.sum_image (fun _ _ _ _ h => (Fin.strictMono_succAbove a).injective h)

/-- C172：最後の非活動位置の削除では、直前同色位置の重みを取り除く。 -/
lemma caesura_sum_erase_final {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (a : Fin (N + 1)) (ha : ¬Surjection.Caesura v a)
    (hp : (Surjection.previousOccurrences v a).Nonempty) (H : Fin (N + 1) → ℕ) :
    (∑ i ∈ caesuraPositions v, H i) =
      (∑ i ∈ caesuraPositions (Surjection.erase v a), H (a.succAbove i)) +
        H (previousVertex v a hp) := by
  have hm : previousVertex v a hp ∈ caesuraPositions v :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, previousVertex_lt v a hp,
      (previousVertex_value v a hp).symm⟩
  rw [← Finset.sum_erase_add (caesuraPositions v) H hm,
    ← caesuraPositions_erase_final_image v a ha hp]
  congr 1
  exact Finset.sum_image (fun _ _ _ _ h => (Fin.strictMono_succAbove a).injective h)

end SerrePositivity.EInfinity.SimplexCuts
