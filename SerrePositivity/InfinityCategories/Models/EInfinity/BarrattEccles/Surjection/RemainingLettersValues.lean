module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionRemoved

/-!
模型。文献の定義との比較は後で
# 指定値のない語の部分型への持ち上げ

概要：Berger–Fresse §1.5.7 の元の利用可能行の前後を代入用の部分型の文字列へ移す。
方針：既存 remainingLetters が指定値を含まない文字列の全ての値を保持することを示す。
規約：元の順序と重複を変えない。
使われ方：実際の一行の分割から substitute_one_slot の入力を構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定値のない文字列は remainingLetters の値リストで復元される（BF §1.5.7）。
方針：各先頭で指定値と異なる分岐を選び、後続に帰納する。
規約：部分型へ持ち上げるだけで文字を消さない。
使われ方：元の行の前後を一出現代入の部分型リストとして使う。 -/
lemma remainingLetters_values_of_not_mem {m : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (hk : k ∉ xs) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k xs).map Subtype.val = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha : a ≠ k := by intro he; exact hk (List.mem_cons.mpr (Or.inl he.symm))
    have ht : k ∉ xs := fun h => hk (List.mem_cons_of_mem _ h)
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters, List.filterMap_cons, dite_eq_right ha, List.map_cons]
    exact congrArg (List.cons a) (ih ht)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
