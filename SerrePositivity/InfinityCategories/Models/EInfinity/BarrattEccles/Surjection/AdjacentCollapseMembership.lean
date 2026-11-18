module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

/-!
模型。文献の定義との比較は後で
# 連続重複縮約による所属値の保存

概要：Berger–Fresse §1.5.8 の外側復元で全射性と行末の再出現を縮約後へ移す。
方針：prepend が同じ文字のコピーを省いても値の所属は変わらないことを帰納的に使う。
規約：出現回数は変わるが、少なくとも一回の出現は保存する。
使われ方：元の合成語から外側語への全射性と再出現を証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：先頭付加の所属は追加文字か元の所属（BF §1.5.8）。
方針：後続の先頭が追加文字に等しいかで分け、重複する選択肢を省く。
規約：後続は縮約済みでなくてもよい。
使われ方：縮約の各段階で全ての値の所属を保存する。 -/
lemma mem_prepend (a b : α) (xs : List α) :
    a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend b xs ↔ a = b ∨ a ∈ xs := by
  cases xs with
  | nil => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend]
  | cons c xs => by_cases h : b = c <;> simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend, h]

/-- 概要：縮約前後で文字の所属は一致する（BF §1.5.8）。
方針：元の語で帰納し、先頭付加の所属公式を使う。
規約：非連続の同値も含め、一回以上の出現だけを比較する。
使われ方：復元外側語の全射性と各行末の後続での再出現を導く。 -/
lemma mem_collapse (a : α) (xs : List α) : a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse xs ↔ a ∈ xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.mem_prepend, ih, List.mem_cons]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse
