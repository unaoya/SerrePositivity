module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CaesuraVertexDeletion
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
模型。文献の定義との比較は後で
# 同じcaesura削除集合の重み付き和

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
既存の一位置削除の集合等式を、位置指数で使う重み付き有限和へ運ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C171：活動位置の削除では、その位置の重みだけを取り除く。 -/
lemma caesura_sum_erase_active {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (a : Fin (N + 1)) (ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v a) (H : Fin (N + 1) → ℕ) :
    (∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions v, H i) =
      (∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v a), H (a.succAbove i)) + H a := by
  have hm : a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
  rw [← Finset.sum_erase_add (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions v) H hm,
    ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions_erase_active_image v a ha]
  congr 1
  exact Finset.sum_image (fun _ _ _ _ h => (Fin.strictMono_succAbove a).injective h)

/-- C172：最後の非活動位置の削除では、直前同色位置の重みを取り除く。 -/
lemma caesura_sum_erase_final {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (a : Fin (N + 1)) (ha : ¬_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v a)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v a).Nonempty) (H : Fin (N + 1) → ℕ) :
    (∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions v, H i) =
      (∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v a), H (a.succAbove i)) +
        H (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex v a hp) := by
  have hm : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex v a hp ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions v :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex_lt v a hp,
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex_value v a hp).symm⟩
  rw [← Finset.sum_erase_add (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions v) H hm,
    ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions_erase_final_image v a ha hp]
  congr 1
  exact Finset.sum_image (fun _ _ _ _ h => (Fin.strictMono_succAbove a).injective h)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
