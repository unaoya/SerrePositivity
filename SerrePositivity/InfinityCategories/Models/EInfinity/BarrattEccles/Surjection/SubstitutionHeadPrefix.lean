module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalLabels
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Substitution

/-!
模型。文献の定義との比較は後で
# 指定値を選択末尾までに一度だけ使う代入の先頭部分

概要：Berger–Fresse §1.5.7 の水平行の先頭選択では内側の先頭文字だけを使う。
方針：選択長さで帰納し、指定値に達したら選択はその文字で止まることを使う。
規約：選択末尾より前には指定値がない。
使われ方：最終除外前の水平成分の一段の実際の出力を計算する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：短い先頭部分の不出現は長い先頭部分の不出現から従う（BF §1.5.7）。
方針：短い take を長い take の take として読む。
規約：文字列は任意。
使われ方：水平行の末尾以外の除外部分へ不出現を渡す。 -/
lemma not_mem_take_of_le {α : Type*} (xs : List α) (a : α) {i j : ℕ}
    (hij : i ≤ j) (h : a ∉ xs.take j) : a ∉ xs.take i := by
  intro hm
  have ht : (xs.take j).take i = xs.take i := by rw [List.take_take, Nat.min_eq_left hij]
  exact h (List.mem_of_mem_take (ht.symm ▸ hm))

/-- 概要：指定値が選択末尾より前にないと代入の選択語は水平ラベル写像（BF §1.5.7）。
方針：外側先頭が指定値なら長さ一、異なれば元の残りラベルとして帰納する。
規約：内側語は先頭文字を持ち、残りは任意。
使われ方：内側の未選択末尾を消さずに水平選択を進める。 -/
lemma substitute_head_prefix {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (ys : List (Fin n)) (xs : List (Fin (m + 1))) (r : ℕ)
    (hb : r ≤ xs.length) (hk : k ∉ xs.take (r - 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs [b :: ys]).take r = (xs.take r).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) := by
  induction r generalizing xs with
  | zero => simp only [List.take_zero, List.map_nil]
  | succ r ih =>
    cases xs with
    | nil => simp only [List.length_nil] at hb; omega
    | cons a xs =>
      by_cases ha : a = k
      · subst a
        have hr : r = 0 := by
          by_contra hn
          have hm : k ∈ (k :: xs).take r := by cases r <;> simp_all
          exact hk (by simpa only [Nat.add_sub_cancel] using hm)
        subst r
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons, List.tail_cons,
          List.map_cons, List.cons_append, List.take_succ_cons, List.take_zero, List.map_nil,
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel_slot]
      · have htail : k ∉ xs.take (r - 1) := by
          cases r with
          | zero => simp
          | succ r =>
            have hh : k ≠ a ∧ k ∉ xs.take r := by
              simpa only [Nat.add_sub_cancel, List.take_succ_cons, List.mem_cons, not_or] using hk
            simpa only [Nat.add_sub_cancel] using hh.2
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right ha, List.take_succ_cons, List.take_succ_cons, List.map_cons,
          ih xs (by simp only [List.length_cons] at hb; omega) htail]
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel, dite_eq_right ha]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
