module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.GridRowBlocks

/-!
模型。文献の定義との比較は後で
# 全融合行列を元の所属行の格子座標列へ同定する

概要：Berger–Fresse §1.5.7 の実際の全融合行列を、内外成分の格子座標列への map で表示する。
方針：共有行の一致で削除するコピーを前半末尾へ移し、水平・垂直の座標表示を反復する。
規約：出力語の一致と同じく共有頂点は一度だけ残す。
使われ方：残る compositionPath の座標列との純粋な組合せ的照合。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：全融合行列を前半末尾を省く連結で表示（BF §1.5.7）。
方針：両境界の共有行一致を使い、二つの実際の融合の第一射影を移す。
規約：次の水平の共有先頭を残す。
使われ方：実際の経路頂点列と同じ連結規則に揃える。 -/
lemma fusedRows_fst_dropLast_step {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : Fin c.count) : (c.fusedRows i.val).map Prod.fst =
      ((c.horizontalRows i.val).map Prod.fst).dropLast ++
        ((c.verticalRows i).map Prod.fst).dropLast ++ (c.fusedRows (i.val + 1)).map Prod.fst := by
  have hh : c.horizontalRows i.val ≠ [] := by
    have := c.horizontalRows_length i.val
    intro he; rw [he] at this; simp only [List.length_nil] at this; omega
  have hv : c.verticalRows i ≠ [] := by
    have := c.verticalRows_length i
    intro he; rw [he] at this; simp only [List.length_nil] at this; omega
  have hn := c.fusedRows_nonempty_head (i.val + 1) (by have := i.isLt; omega)
  have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_ne_nil _ _ hv hn.1
  have hjv : ((c.verticalRows i).map Prod.fst).getLast? =
      ((c.fusedRows (i.val + 1)).map Prod.fst).head? := by
    rw [hn.2]
    exact c.vertical_horizontal_join i
  have hjh : ((c.horizontalRows i.val).map Prod.fst).getLast? =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary (c.verticalRows i) (c.fusedRows (i.val + 1))).map Prod.fst).head? := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_head _ _ hv hn.1]
    exact c.horizontal_vertical_join i
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedRows, dite_eq_left i.isLt, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_fst_dropLast _ _ hh hm hjh,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_fst_dropLast _ _ hv hn.1 hjv, List.append_assoc]

/-- 概要：元の成分境界から作る全融合表の全格子座標（BF §1.5.7）。
方針：水平・垂直の共有末尾を省き、最後の水平は全部残す。
規約：元の語と分割から計算し、行長の証明書の選択を使わない。
使われ方：実際の compositionPath の成分座標列へ照合する。 -/
def fusedGridVertices {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    List (ℕ × ℕ) :=
  if hi : i < c.count then
    (c.horizontalGridVertices i).dropLast ++ (c.verticalGridVertices ⟨i, hi⟩).dropLast ++
      c.fusedGridVertices (i + 1)
  else c.horizontalGridVertices c.count
termination_by c.count - i
decreasing_by omega

/-- 概要：実際の全融合行列は元の全格子座標への置換部分合成（BF §1.5.7）。
方針：成分の行列表示と前半末尾を省く実際の融合式で後ろから帰納する。
規約：経路座標列との一致は入力に要求しない。
使われ方：経路との残る比較を座標列の等式だけへ帰着する。 -/
lemma fusedRows_eq_grid {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : ℕ) (hi : i ≤ c.count) :
    (c.fusedRows i).map Prod.fst = (c.fusedGridVertices i).map c.rowAtGrid := by
  by_cases hlt : i < c.count
  · conv_rhs => rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedGridVertices, dite_eq_left hlt]
    rw [c.fusedRows_fst_dropLast_step ⟨i, hlt⟩, c.horizontalRows_eq_grid,
      c.verticalRows_eq_grid, c.fusedRows_eq_grid (i + 1) (by omega)]
    simp only [List.map_append, List.map_dropLast]
  · have he : i = c.count := by omega
    subst i
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedRows, dite_eq_right (Nat.lt_irrefl _), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedGridVertices,
      dite_eq_right (Nat.lt_irrefl _), c.horizontalRows_eq_grid]
termination_by c.count - i
decreasing_by omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData
