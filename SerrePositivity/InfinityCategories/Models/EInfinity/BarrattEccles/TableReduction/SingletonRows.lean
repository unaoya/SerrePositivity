module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DegenerateRows

/-!
模型。文献の定義との比較は後で
# 一文字の行の削除と抽出結果の削除

概要：Berger–Fresse §1.4.4 の一文字の行を消す操作を reduceRows で証明する。
方針：一文字の行は除外リストを変えず、前の行の抽出を同じまま再構成できる。
規約：行長と語は一般のリストで、まだ符号や Schedule の付け替えは扱わない。
使われ方：削除和のうち頂点境界に対応する項を同定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：一行の長さ条件と後続の成功から抽出成功を再構成（BF §1.3.1）。
方針：reduceRows の定義の肯定分岐を評価する。
規約：先頭に選択された文字列を加える。
使われ方：後続 table の変更を先行行の前へ戻す。 -/
lemma reduceRows_cons_of_success (row : List α) (r : ℕ)
    (rest : List (List α × ℕ)) (removed tail : List α)
    (hr : 0 < r) (hb : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) = some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r) :: rest) removed = some ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r ++ tail) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows]
  rw [ite_eq_left ⟨hr, hb⟩, h]
  rfl

/-- 概要：先頭の一文字行は除外を変えずに一文字を加える（BF §1.4.4）。
方針：take(1−1) が空であることを一行の成功条件へ適用する。
規約：抽出の成功を仮定し、選択された文字の存在を得る。
使われ方：一文字行の削除とその文字の削除の基本的な対応。 -/
lemma reduceRows_singleton_success (row : List α) (rest : List (List α × ℕ))
    (removed out : List α) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, 1) :: rest) removed = some out) :
    ∃ a tail, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest removed = some tail ∧ out = a :: tail := by
  obtain ⟨_, hb, tail, ht, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
  simp only [Nat.sub_self, List.take_zero, List.append_nil] at ht
  cases hx : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row with
  | nil => simp only [hx, List.length_nil] at hb; omega
  | cons a xs =>
    refine ⟨a, tail, ht, ?_⟩
    simpa only [hx, List.take_succ_cons, List.take_zero, List.singleton_append] using he

/-- 概要：任意の位置の一文字行の削除は出力の対応する一文字を削除（BF §1.4.4）。
方針：先行行で帰納し、一文字行の除外状態の不変性を使う。
規約：前後の出力部分を同時に指定する存在命題。
使われ方：一文字行の境界項を一つの頂点を除いた table の項へ移す。 -/
lemma reduceRows_delete_singleton (before : List (List α × ℕ)) (row : List α)
    (rest : List (List α × ℕ)) (removed out : List α)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ (row, 1) :: rest) removed = some out) :
    ∃ pre a post, out = pre ++ a :: post ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ rest) removed = some (pre ++ post) := by
  induction before generalizing removed out with
  | nil =>
    obtain ⟨a, tail, ht, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_singleton_success row rest removed out h
    exact ⟨[], a, tail, he, ht⟩
  | cons p before ih =>
    obtain ⟨hr, hb, tail, ht, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
    obtain ⟨pre, a, post, hp, hc⟩ := ih _ _ ht
    refine ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed p.1).take p.2 ++ pre, a, post, ?_, ?_⟩
    · rw [he, hp, List.append_assoc]
    · have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success p.1 p.2 (before ++ rest) removed
        (pre ++ post) hr hb hc
      simpa only [List.cons_append, List.append_assoc] using hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
