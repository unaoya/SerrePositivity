module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowBoundary
public import Mathlib.Data.List.Chain

/-!
模型。文献の定義との比較は後で
# 同じ隣接行の抽出結果の退化

概要：Berger–Fresse §1.4.1 の等しい隣接置換を持つ table の出力の退化を証明する。
方針：二行目が一行目の最後の文字から始まることを、抽出の成功条件から導く。
規約：退化性は隣接する文字の非一致の IsChain の否定で表す。
使われ方：退化な BE 単体で TR の各項が零になることを示す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：一行の抽出成功を長さ条件と後続行の成功へ分解する（BF §1.3.1）。
方針：条件分岐と Option.map の成功条件を取り出す。
規約：語と除外リストを明示する。
使われ方：隣接する二行の境界を追跡する。 -/
lemma reduceRows_cons_success (row : List α) (r : ℕ)
    (rest : List (List α × ℕ)) (removed out : List α)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r) :: rest) removed = some out) :
    0 < r ∧ r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length ∧
      ∃ tail, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) =
        some tail ∧ out = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r ++ tail := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows] at h
  split at h
  · rename_i hr
    obtain ⟨tail, ht, he⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hr.1, hr.2, tail, ht, he.symm⟩
  · simp at h

/-- 概要：先頭の二行が同じ置換なら出力は隣接重複を持つ（BF §1.4.1）。
方針：二行の長さを正とし、一行目の最後と二行目の先頭を同じ添字で評価する。
規約：行は重複のない文字列。後続の行には条件を課さない。
使われ方：任意の位置の退化な頂点の処理の基礎となる。 -/
lemma reduceRows_same_head_not_isChain (row : List α) (hn : row.Nodup) (r s : ℕ)
    (rest : List (List α × ℕ)) (removed out : List α)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r) :: (row, s) :: rest) removed = some out) :
    ¬ out.IsChain (· ≠ ·) := by
  obtain ⟨hr, hb, tail, ht, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
  obtain ⟨hs, _, tail₂, _, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ ht
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take removed row hn]
  cases r with
  | zero => omega
  | succ k =>
    simp only [Nat.add_sub_cancel]
    have hk : k < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := by omega
    rw [← List.take_concat_get' _ k hk, List.drop_eq_getElem_cons hk]
    cases s with
    | zero => omega
    | succ j =>
      simp only [List.take_succ_cons, List.append_assoc, List.singleton_append]
      intro hc
      exact (List.isChain_append_cons_cons.mp hc).2.1 rfl

/-- 概要：任意の位置で同じ隣接行を持つ table の出力は退化（BF §1.4.1）。
方針：先行行を帰納的に剥がし、後続部分の隣接非一致へ帰着する。
規約：先行行と後続行には重複のないことを要求しない。
使われ方：置換列の任意の隣接退化に適用する。 -/
lemma reduceRows_same_adjacent_not_isChain (before : List (List α × ℕ))
    (row : List α) (hn : row.Nodup) (r s : ℕ) (rest : List (List α × ℕ))
    (removed out : List α)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ (row, r) :: (row, s) :: rest) removed = some out) :
    ¬ out.IsChain (· ≠ ·) := by
  induction before generalizing removed out with
  | nil => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_same_head_not_isChain row hn r s rest removed out h
  | cons p before ih =>
    obtain ⟨_, _, tail, ht, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
    intro hc
    exact ih _ _ ht hc.right_of_append

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
