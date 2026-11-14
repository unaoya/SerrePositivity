module

public import SerrePositivity.EInfinity.SimplexCuts.VertexLists
public import SerrePositivity.EInfinity.Surjection.OccurrenceOrder

/-!
# 元の指定色の出現集合の濃度

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の同じ位置の列挙の補助。
元の昇順リストと元の出現回数を照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の出現集合の濃度は、同じ昇順リストの出現回数（BF §1.2.4）。 -/
lemma occurrences_card_eq_count {r l : ℕ} (v : Fin l → Fin r) (a : Fin r) :
    (Surjection.occurrences v a).card = Surjection.occurrenceCount v a := by
  have hs : (Surjection.occurrences v a).sort (· ≤ ·) = Surjection.occurrencePositions v a :=
    sort_filter_univ l (fun i => v i = a)
  calc
    _ = ((Surjection.occurrences v a).sort (· ≤ ·)).length := (Finset.length_sort _).symm
    _ = _ := by rw [hs, Surjection.occurrencePositions_length]

end SerrePositivity.EInfinity.SimplexCuts
