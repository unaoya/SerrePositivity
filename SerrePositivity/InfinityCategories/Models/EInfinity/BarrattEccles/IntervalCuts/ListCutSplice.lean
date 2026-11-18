module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ListCutValidity
public import Mathlib.Data.List.TakeDrop

/-!
模型。文献の定義との比較は後で
# 三つの語の連結の内側での非零切断

概要：Berger–Fresse §2.2.6 の一出現挿入の切断を、前半・内側・後半のリストで扱う。
方針：内側までの take・drop を計算し、左右の重複消滅とラベルの非交差を結ぶ。
規約：前半と後半のラベルは重なってよいが、それぞれ内側とは交わらない。
使われ方：一出現の切断点色への挿入で合成切断の非退化性を証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

/-- 概要：三ブロックの内側までの接頭語（BF §2.2.6）。
方針：前半の全長を除いて内側語の指定長を取る。
規約：指定長は内側語長以下。
使われ方：一出現挿入の左側切断の評価。 -/
lemma splice_take_inside {α : Type*} (pre inner post : List α) (q : ℕ)
    (hq : q ≤ inner.length) :
    (pre ++ inner ++ post).take (pre.length + q) = pre ++ inner.take q := by
  rw [List.append_assoc, List.take_length_add_append,
    List.take_append_of_le_length hq]

/-- 概要：三ブロックの内側からの接尾語（BF §2.2.6）。
方針：前半の全長と内側の先行部分を除く。
規約：指定開始位置は内側語長以下。
使われ方：一出現挿入の右側切断の評価。 -/
lemma splice_drop_inside {α : Type*} (pre inner post : List α) (q : ℕ)
    (hq : q ≤ inner.length) :
    (pre ++ inner ++ post).drop (pre.length + q) = inner.drop q ++ post := by
  rw [List.append_assoc, List.drop_length_add_append,
    List.drop_append_of_le_length hq]

/-- 概要：非交差な外側ラベルを前後へ付けても内側の非零切断を保つ（BF §2.2.6）。
方針：左右の切断を二ブロックへ分け、各重複消滅とラベル非交差で連結する。
規約：切断点は内側の左右両方に含む。
使われ方：実際の合成語の左右 Nodup 条件の供給。 -/
lemma splice_cut_nodup {α : Type*} (pre inner post : List α) (q : Fin inner.length)
    (hpre : pre.Nodup) (hpost : post.Nodup)
    (hL : (inner.take (q.val + 1)).Nodup) (hR : (inner.drop q.val).Nodup)
    (hdL : pre.Disjoint inner) (hdR : inner.Disjoint post) :
    ((pre ++ inner ++ post).take (pre.length + q.val + 1)).Nodup ∧
      ((pre ++ inner ++ post).drop (pre.length + q.val)).Nodup := by
  constructor
  · rw [Nat.add_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.splice_take_inside pre inner post _ (by have := q.isLt; omega)]
    exact hpre.append hL
      (List.disjoint_of_subset_right (List.take_sublist _ _).subset hdL)
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.splice_drop_inside pre inner post _ q.isLt.le]
    exact hR.append hpost
      (List.disjoint_of_subset_left (List.drop_sublist _ _).subset hdR)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
