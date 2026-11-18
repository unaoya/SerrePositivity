module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.MovedRowBoundary
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DegenerateRows

/-!
模型。文献の定義との比較は後で
# 非退化な table 出力による行長の強制

概要：Berger–Fresse §1.4.3 の一文字を移動した二行での切断位置の一意性。
方針：現在の除外後の行を比較し、誤った切断で同じ文字が境界に連続することを使う。
規約：除外リストと後続行は任意。仮定は除外後の二行の具体的な移動の形。
使われ方：標準頂点列の TR の非零項の行長を順に確定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：誤った行長で成功した table 出力は退化（BF §1.4.3）。
方針：二行の抽出を展開し、前行の末尾と次行の先頭の一致を導く。
規約：指定する正しい行長は pre.length+1。
使われ方：非退化出力ではこの長さ以外を排除する。 -/
lemma reduceRows_wrong_move_not_isChain (row next removed pre mid tail : List α) (a : α)
    (hrow : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row = pre ++ a :: (mid ++ tail))
    (hnext : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed next = pre ++ mid ++ a :: tail)
    (hn : (pre ++ a :: (mid ++ tail)).Nodup) (r s : ℕ)
    (rest : List (List α × ℕ)) (out : List α) (hwrong : r ≠ pre.length + 1)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r) :: (next, s) :: rest) removed = some out) :
    ¬ out.IsChain (· ≠ ·) := by
  obtain ⟨hr, hb, firstTail, ht, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
  rw [hrow] at hb ht ⊢
  obtain ⟨hs, _, secondTail, _, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ ht
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_append, hnext]
  cases r with
  | zero => omega
  | succ k =>
    simp only [Nat.add_sub_cancel]
    have hk : k < (pre ++ a :: (mid ++ tail)).length := by omega
    have hw : k ≠ pre.length := by omega
    have hh := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_moved_wrong_cut_head pre mid tail a hn k hk hw
    obtain ⟨suffix, he⟩ := List.head?_eq_some_iff.mp hh
    rw [he, ← List.take_concat_get' _ k hk]
    cases s with
    | zero => omega
    | succ j =>
      simp only [List.take_succ_cons, List.append_assoc, List.singleton_append]
      intro hc
      exact (List.isChain_append_cons_cons.mp hc).2.1 rfl

/-- 概要：非退化出力を持つ行長は移動する文字の位置に強制される（BF §1.4.3）。
方針：他の行長は境界で隣接重複を持つという補題の対偶を使う。
規約：先行の除外リストは任意でよい。
使われ方：全射語の標準逆像の TR の和を一項に帰着する。 -/
lemma reduceRows_forces_move_length (row next removed pre mid tail : List α) (a : α)
    (hrow : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row = pre ++ a :: (mid ++ tail))
    (hnext : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed next = pre ++ mid ++ a :: tail)
    (hn : (pre ++ a :: (mid ++ tail)).Nodup) (r s : ℕ)
    (rest : List (List α × ℕ)) (out : List α)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r) :: (next, s) :: rest) removed = some out)
    (hc : out.IsChain (· ≠ ·)) : r = pre.length + 1 := by
  by_contra hw
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_wrong_move_not_isChain row next removed pre mid tail a
    hrow hnext hn r s rest out hw h hc

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
