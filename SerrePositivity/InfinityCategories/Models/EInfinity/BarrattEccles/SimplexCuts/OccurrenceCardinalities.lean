module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VertexLists
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrenceOrder

/-!
模型。文献の定義との比較は後で
# 元の指定色の出現集合の濃度

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の同じ位置の列挙の補助。
元の昇順リストと元の出現回数を照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の出現集合の濃度は、同じ昇順リストの出現回数（BF §1.2.4）。 -/
lemma occurrences_card_eq_count {r l : ℕ} (v : Fin l → Fin r) (a : Fin r) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v a).card = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v a := by
  have hs : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v a).sort (· ≤ ·) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrencePositions v a :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sort_filter_univ l (fun i => v i = a)
  calc
    _ = ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences v a).sort (· ≤ ·)).length := (Finset.length_sort _).symm
    _ = _ := by rw [hs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrencePositions_length]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
