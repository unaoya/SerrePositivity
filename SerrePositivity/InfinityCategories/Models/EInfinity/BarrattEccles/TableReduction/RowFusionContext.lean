module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowFusion
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TwoRowExtraction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TransferPrefixLift

/-!
模型。文献の定義との比較は後で
# 表の途中の共有頂点行の融合

概要：Berger–Fresse §1.5.7 の成分接合の融合を任意の先行抽出の後で適用する。
方針：元の成功を接合前で切り、同じ二行を融合し、先行証跡を戻す。
規約：共有文字の前のコピー一つを消し、元の二行後の状態を保つ。
使われ方：全成分の合成表を共有頂点一つの経路表へ順に移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：任意の先行部分の後の同じ二行を融合した表は共有文字一つを除いた語を返す（BF §1.5.7）。
方針：接合の局所融合成功を元の先行証跡へ戻し、削除位置を先行出力長だけずらす。
規約：先行部分の行長の和と現在行長 r で削除位置を指定する。
使われ方：合成経路の各接合を実際の全表の成功へ反映する。 -/
lemma rowFusion_in_context (before : List (List α × ℕ)) (initial row : List α)
    (hn : row.Nodup) (r s : ℕ) (rest : List (List α × ℕ)) (out : List α)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ (row, r) :: (row, s) :: rest) initial = some out) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ (row, r + s - 1) :: rest) initial =
      some (out.eraseIdx ((before.map Prod.snd).sum + (r - 1))) := by
  obtain ⟨picked, removed, localOut, hp, hlocal, hout⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionPrefix_of_reduceRows before _ initial out h
  obtain ⟨hr, hbr, middle, hm, hlocalOut⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ hlocal
  obtain ⟨hs, hbs, tail, ht, hmiddle⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ hm
  have hf := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowFusion_success removed row hn r s hr hbr hs hbs rest tail ht
  have hsuccess := hp.append ((row, r + s - 1) :: rest) _ hf
  have hlen : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).length = r := List.length_take_of_le hbr
  have hlast : r - 1 + 1 = ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).length := by rw [hlen]; omega
  have hbound : r - 1 < ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).length := by rw [hlen]; omega
  have hword : out.eraseIdx ((before.map Prod.snd).sum + (r - 1)) =
      picked.flatten ++ (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).dropLast ++
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) row).take s ++ tail)) := by
    rw [hout, hlocalOut, hmiddle, ← hp.output_length, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.eraseIdx_prefix_add,
      List.eraseIdx_append, ite_eq_left hbound, List.eraseIdx_eq_dropLast hlast]
  rw [hword]
  exact hsuccess

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
