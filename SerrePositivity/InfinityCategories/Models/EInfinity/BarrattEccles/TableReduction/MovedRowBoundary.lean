module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowBoundary

/-!
模型。文献の定義との比較は後で
# 一文字を移動した行での誤った切断位置

概要：Berger–Fresse §1.4.3 の table の境界重複を一般の一文字の移動で証明する。
方針：移動位置より前の切断は共通の先頭を残し、後の切断は移動文字を除外する。
規約：先行行は重複しない。正しい切断は移動する文字の直後。
使われ方：非退化な table の行長が指定した長さに強制されることを示す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：移動する文字を除外すると二行は一致（BF §1.4.3）。
方針：filter を連結に分配し、移動文字の項を零長の列へ簡約する。
規約：他の値の除外条件には制約を課さない。
使われ方：指定より後の切断で残る語を元の行の尾部と比較する。 -/
lemma available_move_of_mem (removed pre mid tail : List α) (a : α) (ha : a ∈ removed) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (pre ++ a :: (mid ++ tail)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (pre ++ mid ++ a :: tail) := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_append, ha, List.append_assoc]

/-- 概要：指定外の切断では次行の先頭が前行の末尾と一致（BF §1.4.3）。
方針：切断が移動文字の前か後かで分岐し、共通先頭または除外後の同じ尾部を使う。
規約：k は前行の長さから 1 を引いた値。
使われ方：次の行との境界で隣接重複があることを導く。 -/
lemma available_moved_wrong_cut_head (pre mid tail : List α) (a : α)
    (hn : (pre ++ a :: (mid ++ tail)).Nodup) (k : ℕ)
    (hk : k < (pre ++ a :: (mid ++ tail)).length) (hwrong : k ≠ pre.length) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available ((pre ++ a :: (mid ++ tail)).take k)
      (pre ++ mid ++ a :: tail)).head? = some ((pre ++ a :: (mid ++ tail))[k]) := by
  by_cases hbefore : k < pre.length
  · rw [List.take_append_of_le_length (Nat.le_of_lt hbefore)]
    have hp := (List.nodup_append.mp hn).1
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filter_not_mem_take pre hp k]
    rw [List.drop_eq_getElem_cons hbefore]
    simp only [List.cons_append, List.head?_cons, List.getElem_append_left hbefore]
  · have hafter : pre.length < k := by omega
    have ha : a ∈ (pre ++ a :: (mid ++ tail)).take k := by
      have hs : 0 < k - pre.length := by omega
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
      simp only [List.take_append, hj, List.take_succ_cons, List.mem_append, List.mem_cons,
        true_or, or_true]
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_move_of_mem _ pre mid tail a ha]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filter_not_mem_take _ hn k, List.head?_drop, List.getElem?_eq_getElem hk]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
