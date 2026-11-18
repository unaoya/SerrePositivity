module

public import Mathlib.Data.List.TakeDrop

/-!
模型。文献の定義との比較は後で
# 複数行を跨ぐ閉区間の連結語

概要：Berger–Fresse §1.5.7 の始行末尾・中間行・終行先頭を元の連結語から取り出す。
方針：始行内で drop した後、中間全体と終行先頭まで take する。
規約：終行先頭の要求長は終行長以下。
使われ方：元の二行分割の出力を成分の実際の部分語へ照合する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：始行内から終行先頭までの語は三部分の連結（BF §1.5.7）。
方針：drop の連結公式と二回の全長 take を使う。
規約：要求する終行先頭長は零でもよい。
使われ方：複数行成分の選択語の平坦化の計算。 -/
lemma interval_of_three_blocks {α : Type*} (left middle right tail : List α)
    (a b : ℕ) (ha : a ≤ left.length) (hb : b ≤ right.length) :
    ((left ++ (middle ++ (right ++ tail))).drop a).take
        (left.length - a + middle.length + b) =
      left.drop a ++ (middle ++ right.take b) := by
  rw [List.drop_append_of_le_length ha]
  have he : left.length - a + middle.length + b =
      (left.drop a).length + (middle.length + b) := by
    simp only [List.length_drop, Nat.add_assoc]
  rw [he, List.take_length_add_append, List.take_length_add_append,
    List.take_append_of_le_length hb]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
