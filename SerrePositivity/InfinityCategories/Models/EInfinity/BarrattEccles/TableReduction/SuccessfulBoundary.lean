module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DegenerateRows

/-!
模型。文献の定義との比較は後で
# 非退化な成功表の隣接行の境界

概要：Berger–Fresse §1.5.8 の非退化出力で、前行末と次行頭が異なることを取り出す。
方針：元の成功から正の行長を得て、出力の境界二文字を明示する。
規約：行の非重複性や置換由来であることは要求しない。
使われ方：水平移動の両側の内側ラベルが同じ値になる場合を排除する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：実際の非退化な成功出力の隣接行の末尾・先頭は異なる（BF §1.5.8）。
方針：前行の take を末尾で分け、次行の正の take の先頭と隣接させる。
規約：前行末は可用行の r−1 番目、次行頭は更新後の可用行の head? で指定する。
使われ方：同じ内側置換を持つ合成二行の境界の非退化性を復元する。 -/
lemma reduceRows_boundary_ne (row row' : List α) (r s : ℕ)
    (rest : List (List α × ℕ)) (removed out : List α) (a b : α)
    (he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row)[r - 1]? = some a)
    (hh : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) row').head? = some b)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r) :: (row', s) :: rest) removed = some out)
    (hc : out.IsChain (· ≠ ·)) : a ≠ b := by
  obtain ⟨hr, _, tail, ht, ho⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
  obtain ⟨hs, _, tail', _, ho'⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ ht
  obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp he
  have htake : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1) ++ [a] := by
    have heq : r - 1 + 1 = r := by omega
    simpa only [heq, hv] using (List.take_append_getElem hi).symm
  obtain ⟨ys, hy⟩ := List.head?_eq_some_iff.mp hh
  rw [ho, ho', htake, hy] at hc
  cases s with
  | zero => omega
  | succ s =>
    simp only [List.take_succ_cons, List.append_assoc, List.singleton_append] at hc
    exact (List.isChain_append_cons_cons.mp hc).2.1

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
