module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowBoundary
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix

/-!
模型。文献の定義との比較は後で
# 一行内の閉区間を共有端点を残して抽出する

概要：Berger–Fresse §1.5.7 の行内部で切られた成分の抽出を構成する。
方針：開始位置より前を除外し、終了位置の文字を最後として選ぶ。
規約：区間の両端を含み、終了文字自身は次の除外状態へ加えない。
使われ方：同じ行に含まれる成分と、複数行にまたがる成分の両端を処理する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：一行の開始前と終了前の除外更新は先頭部分の連結で一致（BF §1.5.7）。
方針：元の行の重複のなさで現在行を drop し、take_add で先頭部分を戻す。
規約：開始位置は終了位置以下。
使われ方：閉区間の最後の文字を残す正確な終状態。 -/
lemma rowInterval_removed_eq (removed row : List α) (hn : row.Nodup) (a b : ℕ)
    (hab : a ≤ b) :
    (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take a) ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take a) row).take (b - a) =
        removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take b := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take removed row hn a, List.append_assoc, ← List.take_add,
    Nat.add_sub_of_le hab]

/-- 概要：一行内の閉区間の実際の先行抽出証跡（BF §1.5.7）。
方針：開始位置から終了位置までの正の行長を一行の構成子へ渡す。
規約：終了位置の文字は除外せず保持する。
使われ方：重なる分割の同じ行内の成分を元の行から抽出する。 -/
lemma rowInterval_prefix (removed row : List α) (hn : row.Nodup) (a b : ℕ)
    (hab : a ≤ b) (hb : b < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(row, b - a + 1)] (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take a)
      [((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).drop a).take (b - a + 1)]
      (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take b) := by
  have hr : 0 < b - a + 1 := by omega
  have hlen : b - a + 1 ≤
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take a) row).length := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take removed row hn a, List.length_drop]
    omega
  have hstate := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowInterval_removed_eq removed row hn a b hab
  have ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix []
      ((removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take a) ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take a) row).take (b - a + 1 - 1)) []
      (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take b) := by
    rw [Nat.add_sub_cancel, hstate]
    exact .nil _
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.cons hr hlen ht
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take removed row hn a] using hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
