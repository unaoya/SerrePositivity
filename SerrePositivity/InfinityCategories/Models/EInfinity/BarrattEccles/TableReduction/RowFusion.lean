module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowBoundary
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonRows

/-!
模型。文献の定義との比較は後で
# 共有頂点の同じ二行を一行へ融合する

概要：Berger–Fresse §1.5.7 の水平・垂直成分の共有頂点で重複する置換行を融合する。
方針：後半は前半の末尾から再開し、共有文字を一度だけ数える。
規約：除外終状態は元の二行の逐次更新と厳密に一致する。
使われ方：成分の連結を実際の shuffle 経路の共有頂点一つへ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：同じ行の二つの選択の更新は長さ r+s−1 の一行の更新（BF §1.5.7）。
方針：前半末尾からの drop と take_add で除外先頭部分を連結する。
規約：両方の選択長さは正。
使われ方：共有頂点での行融合の終状態。 -/
lemma rowFusion_removed_eq (removed row : List α) (hn : row.Nodup) (r s : ℕ)
    (hr : 0 < r) (hs : 0 < s) :
    (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) row).take (s - 1) =
        removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r + s - 1 - 1) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take removed row hn, List.append_assoc, ← List.take_add]
  have he : r - 1 + (s - 1) = r + s - 1 - 1 := by omega
  rw [he]

omit [DecidableEq α] in
/-- 概要：同じ行の二選択の共有文字を一度だけ残した語（BF §1.5.7）。
方針：前半の末尾を除き、その位置からの後半を take_add で連結する。
規約：前半の選択は元の行の長さ以内。
使われ方：共有頂点の行融合での出力語。 -/
lemma rowFusion_word_eq (xs : List α) (r s : ℕ) (hr : 0 < r) (hb : r ≤ xs.length) :
    (xs.take r).dropLast ++ (xs.drop (r - 1)).take s = xs.take (r + s - 1) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.dropLast_take_of_le_length xs r hb, ← List.take_add]
  have he : r - 1 + s = r + s - 1 := by omega
  rw [he]

/-- 概要：同じ行の二段の後続から一行に融合した実際の抽出成功（BF §1.5.7）。
方針：二段の終状態を一段の終状態へ移し、共有文字を一度だけ数えた語を返す。
規約：前後の二選択の成功長さ条件を使う。
使われ方：垂直・水平ブロックの接合を実際の一つの頂点行へ融合する。 -/
lemma rowFusion_success (removed row : List α) (hn : row.Nodup) (r s : ℕ)
    (hr : 0 < r) (hbr : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length) (hs : 0 < s)
    (hbs : s ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) row).length)
    (rest : List (List α × ℕ)) (tail : List α)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest
      ((removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) row).take (s - 1)) =
      some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r + s - 1) :: rest) removed =
      some (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).dropLast ++
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) row).take s ++ tail)) := by
  have hb : r + s - 1 ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take removed row hn, List.length_drop] at hbs
    omega
  have ht' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r + s - 1 - 1)) =
      some tail := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowFusion_removed_eq removed row hn r s hr hs] at ht
    exact ht
  have hx := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success row (r + s - 1) rest removed tail (by omega) hb ht'
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take removed row hn]
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowFusion_word_eq (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row) r s hr hbr] at hx
  simpa only [List.append_assoc] using hx

/-- 概要：同じ二行の元の成功から共有文字を一度だけ残す融合成功を得る（BF §1.5.7）。
方針：元の二段の成功条件と後続を取り出し、同じ終状態の融合規則へ渡す。
規約：元の語では接合文字が二度現れ、融合語では前半の末尾を除く。
使われ方：二つの成分ブロックの接合を共有頂点一つの実際の表へ移す。 -/
lemma rowFusion_of_success (removed row : List α) (hn : row.Nodup) (r s : ℕ)
    (rest : List (List α × ℕ)) (out : List α)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r) :: (row, s) :: rest) removed = some out) :
    ∃ tail,
      out = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r ++
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) row).take s ++ tail) ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r + s - 1) :: rest) removed =
        some (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).dropLast ++
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) row).take s ++ tail)) := by
  obtain ⟨hr, hbr, middle, hm, hout⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
  obtain ⟨hs, hbs, tail, ht, hmiddle⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ hm
  refine ⟨tail, ?_, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowFusion_success removed row hn r s hr hbr hs hbs rest tail ht⟩
  rw [hout, hmiddle]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
