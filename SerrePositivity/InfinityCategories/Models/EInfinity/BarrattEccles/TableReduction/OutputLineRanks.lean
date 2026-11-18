module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RawRowEndSigns
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowEndCounts
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.LineRankCounts

/-!
模型。文献の定義との比較は後で
# 抽出された各行の内部の行番号

概要：Berger–Fresse §1.5.7 で使う語の lineRank と実際の table の行添字を同定する。
方針：語の区切り列を行末列へ移し、指定位置より前の行末の個数を数える。
規約：行末自身も同じ行の位置として扱う。
使われ方：出現境界・重なる分割の端点の行番号を元の成功抽出へ接続する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：行末列を持つ語の行番号は先行行末の個数（BF §1.5.7）。
方針：生の区切り列の自然数値のリストを行末列へ置き換える。
規約：自然数位置は語長を超えてもよい。
使われ方：行番号の評価を行のリストの計算へ移す。 -/
lemma lineRank_eq_rowEnd_count {n l : ℕ} (v : Fin l → Fin n)
    (picked : List (List (Fin n))) (hn : ∀ row ∈ picked, row ≠ [])
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions (List.ofFn v) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked) (p : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p = ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked).filter (fun k => k < p)).length := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_eq_rawCaesura_count, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rawCaesuraList_val_eq_rowEnds v picked hn he]
  simp only [List.filter_map, Function.comp_def, List.length_map]

/-- 概要：選択行の内部の lineRank はその実際の行添字（BF §1.5.7）。
方針：指定位置より前には前の行末だけがあり、その個数が行添字になる。
規約：語の全射性・非退化性を要求しない。
使われ方：合成経路の成分次数を元の抽出証跡の区間へ移す。 -/
lemma lineRank_in_picked_row {n l : ℕ} (v : Fin l → Fin n)
    (picked : List (List (Fin n))) (hn : ∀ row ∈ picked, row ≠ [])
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions (List.ofFn v) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked)
    (i : ℕ) (hi : i < picked.length) (j : ℕ) (hj : j < picked[i].length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (((picked.take i).map List.length).sum + j) = i := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.lineRank_eq_rowEnd_count v picked hn he]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions_count_before_in_row picked hn i hi j hj

/-- 概要：成功した table の抽出証跡の区切りは同じ証跡の行末（BF §1.5.7）。
方針：各選択行の分離と出力長の飽和から全非最終行末の再出現を強制する。
規約：任意の指定された成功証跡自身に適用する。
使われ方：存在で取り直した行分割ではなく元の抽出証跡へ行番号を与える。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace.rowEnds {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {picked : List (List (Fin n))}
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] picked) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.repeatPositions picked.flatten = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked := by
  have hs := ht.separatedRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_nodup w r)
  have hn := ht.nonempty
  have hl : picked.length = d + 1 := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn] using ht.length
  have hlen : picked.flatten.length = n + (picked.length - 1) := by
    rw [hl, Nat.add_sub_cancel]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r _ ht.reduceRows
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.repeatPositions_flatten_eq_rowEnds picked hs (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.recurrentEnds_of_length picked hs hn hlen) hn

/-- 概要：元の成功証跡の各行で語の lineRank は行添字（BF §1.5.7）。
方針：同じ証跡の行末と語の出力を照合する。
規約：最終行を含む全行と全内部位置について成立する。
使われ方：成分経路の水平・垂直回数を元の抽出の行に対応させる。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace.lineRank_in_row {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {picked : List (List (Fin n))} (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] picked)
    (v : Fin (n + d) → Fin n) (hout : picked.flatten = List.ofFn v)
    (i : ℕ) (hi : i < picked.length) (j : ℕ) (hj : j < picked[i].length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (((picked.take i).map List.length).sum + j) = i := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.lineRank_in_picked_row v picked ht.nonempty _ i hi j hj
  rw [← hout]
  exact ht.rowEnds

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
