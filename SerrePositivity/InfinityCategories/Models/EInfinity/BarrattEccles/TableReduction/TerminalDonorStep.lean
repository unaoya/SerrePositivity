module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DonorStep

/-!
模型。文献の定義との比較は後で
# 最終行の末尾を削除する局所抽出

概要：Berger–Fresse §1.4.4 の最後の行の末尾の最終出現削除を扱う。
方針：早く除外された末尾を飛ばし、元の選択長を一つ減らす。
規約：後続行が空なので、行通過後の除外状態の一致は要求しない。
使われ方：最終出現削除の相殺で末尾位置も含める。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：最終行の末尾を削除した短い抽出は元の末尾前の部分（BF §1.4.4）。
方針：利用可能行を削除値の前後で分け、一文字の早い除外と take を計算する。
規約：元の選択長は 2 以上で、削除値より後の選択文字は零個。
使われ方：元の最終末尾削除を相殺相手の先行行末削除へ対応させる。 -/
lemma reduceRows_terminal_donor_step (removed row pre post : List α) (a : α)
    (hp : 0 < pre.length) (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row = pre ++ a :: post)
    (hpre : a ∉ pre) (hpost : a ∉ post) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows [(row, pre.length + 1)] removed = some (pre ++ [a]) ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows [(row, pre.length)] (removed ++ [a]) = some pre := by
  have hold := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success row (pre.length + 1) [] removed [] (by omega)
    (by rw [he, List.length_append, List.length_cons]; omega) (by rfl)
  have hnew := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success row pre.length [] (removed ++ [a]) [] hp
    (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_donor_split removed row pre post a he hpre hpost, List.length_append]; omega)
    (by rfl)
  constructor
  · simpa only [he, List.take_length_add_append, List.take_succ_cons, List.take_zero,
      List.append_nil] using hold
  · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_donor_split removed row pre post a he hpre hpost,
      List.take_append_length, List.append_nil] using hnew

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
