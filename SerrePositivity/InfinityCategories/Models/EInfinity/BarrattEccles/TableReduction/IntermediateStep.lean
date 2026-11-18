module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DonorStep

/-!
模型。文献の定義との比較は後で
# 中間行の選択を変えない早い除外

概要：Berger–Fresse §1.4.4 の直前出現と削除行の間で、同じ値を早く除外する。
方針：元の選択部分にない値の filter は、その先行部分を変えない。
規約：行長はそのまま、除外に一文字だけ加える。
使われ方：受け取り行で加えた除外を削除行まで運ぶ。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：先頭 r 文字にない値を除いても先頭 r 文字は同じ（BF §1.4.4）。
方針：リストと r で帰納し、選ばれた先頭文字は消えないことを使う。
規約：r がリスト長を超える場合も含む。
使われ方：中間行の選択と除外部分の不変性を示す。 -/
lemma take_filter_ne_of_not_mem (xs : List α) (a : α) (r : ℕ) (ha : a ∉ xs.take r) :
    (xs.filter (fun x => x ≠ a)).take r = xs.take r := by
  induction r generalizing xs with
  | zero => simp
  | succ r ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      have hxa : x ≠ a := by intro h; subst x; exact ha (by simp)
      have ht : a ∉ xs.take r := by
        intro hm
        exact ha (by simp only [List.take_succ_cons, List.mem_cons]; exact Or.inr hm)
      simp only [List.filter_cons, decide_eq_true_eq, ite_eq_left hxa,
        List.take_succ_cons, ih xs ht]

/-- 概要：早く除外する値が選択部分になければ中間行の出力は同じ（BF §1.4.4）。
方針：一文字の除外を利用可能行の filter として計算する。
規約：元の選択に削除値がないことだけを要求する。
使われ方：全中間行の出力を元のまま保つ。 -/
lemma intermediate_selected_eq (removed row : List α) (a : α) (r : ℕ)
    (ha : a ∉ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row).take r = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_append_singleton]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.take_filter_ne_of_not_mem _ a r ha

/-- 概要：中間行の末尾以外にも早く除外する値はない（BF §1.4.4）。
方針：短い先行部分の所属を元の選択部分へ移す。
規約：長さ r−1 は自然数の切り捨て減算。
使われ方：次の除外状態に加える部分の不変性を示す。 -/
lemma intermediate_excluded_eq (removed row : List α) (a : α) (r : ℕ)
    (ha : a ∉ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row).take (r - 1) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.intermediate_selected_eq
  intro hm
  have he : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).take (r - 1) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) := by
    rw [List.take_take, Nat.min_eq_left (Nat.sub_le r 1)]
  rw [← he] at hm
  exact ha (List.mem_of_mem_take hm)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
