module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowEndPositions

/-!
模型。文献の定義との比較は後で
# 選択行の内部より前の行末の個数

概要：Berger–Fresse §1.5.7 の各成分に含まれる行数を実際の選択行から計算する。
方針：行の列で帰納し、先頭の長さによる位置移動と非最終行末の一個を分離する。
規約：各行は非空で、現在行の末尾自身は先行行末に数えない。
使われ方：成分次数を元の table の行添字の差へ同定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：第 i 行の内部より前の非最終行末はちょうど i 個（BF §1.5.7）。
方針：先頭行では零、後続では先頭行末を一個加えた帰納法。
規約：行の末尾もその行の内部位置として含める。
使われ方：全射語の lineRank を実際の抽出行の添字へ戻す。 -/
lemma rowEndPositions_count_before_in_row {α : Type*} (picked : List (List α))
    (hn : ∀ row ∈ picked, row ≠ []) (i : ℕ) (hi : i < picked.length)
    (j : ℕ) (hj : j < picked[i].length) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked).filter
      (fun p => p < ((picked.take i).map List.length).sum + j)).length = i := by
  induction picked generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons row rest ih =>
    have hr : 0 < row.length := List.length_pos_iff.mpr (hn row (by simp))
    have hrest : ∀ r ∈ rest, r ≠ [] := fun r h => hn r (by simp [h])
    cases i with
    | zero =>
      have hj' : j < row.length := hj
      cases rest with
      | nil => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions]
      | cons next rest =>
        have hfirst : ¬ row.length - 1 < j := by omega
        have htail : (fun p : ℕ => decide (row.length + p < j)) = fun _ => false := by
          funext p
          exact decide_eq_false (by omega)
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
          List.filter_cons, decide_eq_false hfirst, Bool.false_eq_true, ite_false,
          List.filter_map, Function.comp_def, htail, List.filter_false, List.map_nil,
          List.length_nil]
    | succ i =>
      have hi' : i < rest.length := by
        simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hi
      have hj' : j < rest[i].length := hj
      have hb := ih hrest i hi' hj'
      cases rest with
      | nil => simp only [List.length_nil] at hi'; omega
      | cons next rest =>
        have hfirst : row.length - 1 <
            row.length + (((next :: rest).take i).map List.length).sum + j := by omega
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions, List.take_succ_cons, List.map_cons, List.sum_cons,
          List.filter_cons]
        rw [ite_eq_left (decide_eq_true hfirst)]
        simpa only [List.length_cons, List.filter_map, Function.comp_def, Nat.add_assoc,
          Nat.add_lt_add_iff_left, List.length_map] using congrArg (fun x => x + 1) hb

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
